//! Decompose complex rules into bite-sized sub-rules.
//!
//! Each sub-rule is associated to an implicit variable.
//! Decomposition can heavily reduce the complexity of some operations,
//! e.g. to formulate a constraint-solving problem based on (prime) implicants.
//!
//! The approach imnplemented here is strongly related to the
//! [estimation of implicant complexity](Expr::estimate_complexity) where
//! a ```AND``` multiplies the complexity of its two children.
//! Extracting the child with the highest complexity yields an overall additive
//! complexity. A penalty parameter is used to control over-decomposition.
//!
//! Related work: tree decomposition in non-ground ASP programs
//! <https://www.dbai.tuwien.ac.at/research/project/lpopt/thesis.pdf>

use crate::expr::{Expr, ExprNode};
use crate::*;
use std::borrow::Cow;
use std::fmt::{Display, Formatter};
use std::ops::Not;

/// An expression decomposed into subexpressions to spread the implicant complexity.
///
/// This contains a main ("root") expression where some sub-expressions are replaced
/// with dedicated variables.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "pyo3", pyclass(module = "bokit"))]
pub struct DecomposedExpr {
    root: Expr,
    associated: HashMap<Variable, Expr>,
}

/// The prime implicants of a rule decomposed using sub-rules
///
/// Some variables in the patterns of the ("root") implicants correspond to
/// associated variables with their own set of prime implicants.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "pyo3", pyclass(module = "bokit"))]
pub struct DecomposedPrimes {
    root: Primes,
    associated: HashMap<Variable, Primes>,
}

pub trait DecomposeHelper {
    fn set_expr(&mut self, expr: &Expr);
    fn pick_variable(&mut self) -> Variable;
}

struct DecompositionTracker {
    variables: VarSet,
    next_var: Variable,
    penalty: usize,
    expansion_score: usize,
    score: usize,
}

/// Overview of the estimated implicant complexity of a [`DecomposedExpr`]
#[derive(Clone, Debug)]
#[cfg_attr(feature = "pyo3", pyclass(module = "bokit"))]
pub struct DecomposeReport {
    root_score: usize,
    sum_sub_score: usize,
}

#[cfg_attr(feature = "pyo3", pymethods)]
impl DecomposedExpr {
    #[cfg(feature = "pyo3")]
    pub fn __str__(&self) -> String {
        format!("{}", self)
    }

    #[cfg(feature = "pyo3")]
    pub fn __repr__(&self) -> String {
        format!("{}", self)
    }

    pub fn is_expanded(&self) -> bool {
        !self.associated.is_empty()
    }

    pub fn expansion_count(&self) -> usize {
        self.associated.len()
    }

    /// Compute the prime implicants of this system of expressions.
    ///
    /// Construct the corresponding system of prime implicants
    pub fn to_primes(&self) -> DecomposedPrimes {
        DecomposedPrimes::from(self)
    }

    /// Merge this decomposition into a single expression.
    ///
    /// Note that due to automatic simplifications (especially the use of patterns),
    /// the merged expression may differ from the original expression, but they
    /// should still be very similar.
    pub fn merge(&self) -> Expr {
        self.merge_expression(&self.root).into_owned()
    }
}

impl DecomposedExpr {
    pub(crate) fn new(e: &Expr, penalty: usize) -> (Self, DecomposeReport) {
        let cplx = e.estimate_complexity().score().unwrap_or(usize::MAX);
        if cplx < 50 {
            return (
                DecomposedExpr {
                    root: e.clone(),
                    associated: HashMap::default(),
                },
                DecomposeReport {
                    root_score: cplx,
                    sum_sub_score: 0,
                },
            );
        }
        let mut slf = Self {
            root: e.clone(),
            associated: HashMap::new(),
        };

        let e = e.nnf();
        let mut tracker = DecompositionTracker {
            variables: e.get_regulators(),
            next_var: Variable(0),
            penalty,
            expansion_score: 0,
            score: 0,
        };

        let (e, score) = slf.explore(&e, true, &mut tracker);
        tracker.score = score;
        if let Cow::Owned(expr) = e {
            slf.root = expr;
        }

        (slf, tracker.report())
    }

    fn merge_expression<'a>(&self, expr: &'a Expr) -> Cow<'a, Expr> {
        match &expr.node {
            ExprNode::True => None,
            ExprNode::Variable(v) => self.merge_variable(v, expr.value),
            ExprNode::Pattern(p) => self.merge_pattern(p, expr.value),
            ExprNode::Operation(op, children) => {
                self.merge_operation(*op, &children.0, &children.1, expr.value)
            }
        }
        .map_or_else(|| Cow::Borrowed(expr), Cow::Owned)
    }

    fn merge_variable(&self, var: &Variable, value: bool) -> Option<Expr> {
        self.associated
            .get(var)
            .map(|e| if value { e.clone() } else { !e })
    }

    fn merge_pattern(&self, p: &Pattern, value: bool) -> Option<Expr> {
        // TODO: is it worth reconstructing the pattern only if needed?
        let mut core_expr = Expr::from(true);
        let mut expanded_expr = Expr::from(true);
        for (v, b) in p.iter_fixed_values() {
            match (b, self.associated.get(&v)) {
                (true, None) => core_expr = core_expr & v,
                (false, None) => core_expr = core_expr & !v,
                (true, Some(sub)) => expanded_expr = expanded_expr & sub,
                (false, Some(sub)) => expanded_expr = expanded_expr & !sub,
            }
        }
        if expanded_expr.node == ExprNode::True {
            return None;
        }
        let result = core_expr & expanded_expr;
        Some(if value { result } else { !result })
    }

    fn merge_operation(
        &self,
        op: Operator,
        child0: &Expr,
        child1: &Expr,
        value: bool,
    ) -> Option<Expr> {
        let c0 = self.merge_expression(child0);
        let c1 = self.merge_expression(child1);

        if let (Cow::Borrowed(_), Cow::Borrowed(_)) = (&c0, &c1) {
            return None;
        }

        let children = Arc::new((c0.into_owned(), c1.into_owned()));
        Some(Expr {
            value,
            node: ExprNode::Operation(op, children),
        })
    }

    pub fn expansions(&self) -> &HashMap<Variable, Expr> {
        &self.associated
    }

    fn explore<'a>(
        &mut self,
        e: &'a Expr,
        parent_bool: bool,
        tracker: &mut DecompositionTracker,
    ) -> (Cow<'a, Expr>, usize) {
        let b = e.value && parent_bool;
        let fwd = Cow::Borrowed(e);
        match &e.node {
            ExprNode::Variable(_v) => (fwd, 1),
            ExprNode::True => (fwd, b as usize),
            ExprNode::Pattern(p) => (fwd, if b { 1 } else { p.additional_len() }),
            ExprNode::Operation(o, children) => {
                let (mut e1, mut s1) = self.explore(&children.0, b, tracker);
                let (mut e2, mut s2) = self.explore(&children.1, b, tracker);
                if (b && o == &Operator::Or) || (!b && o == &Operator::And) {
                    return (Expr::forward_expr(fwd, *o, b, e1, e2), s1 + s2);
                }

                if s1 > 1 && s2 > 1 {
                    let savings = (s1 - 1) * (s2 - 1);
                    if savings > tracker.penalty {
                        if s1 > s2 {
                            e1 = Cow::Owned(self.extract_sub_expression(tracker, parent_bool, e1));
                            tracker.expansion_score += s1;
                            s1 = 1;
                        } else {
                            e2 = Cow::Owned(self.extract_sub_expression(tracker, parent_bool, e2));
                            tracker.expansion_score += s2;
                            s2 = 1;
                        }
                    }
                }

                (Expr::forward_expr(fwd, *o, b, e1, e2), s1 * s2)
            }
        }
    }

    fn extract_sub_expression(
        &mut self,
        tracker: &mut DecompositionTracker,
        parent_bool: bool,
        e: Cow<Expr>,
    ) -> Expr {
        let var = tracker.pick_var();
        let extracted = if parent_bool {
            e.into_owned()
        } else {
            e.as_ref().not()
        };
        self.associated.insert(var, extracted);
        if parent_bool {
            var.into()
        } else {
            var.not()
        }
    }
}

#[cfg_attr(feature = "pyo3", pymethods)]
impl DecomposedPrimes {
    #[cfg(feature = "pyo3")]
    pub fn __str__(&self) -> String {
        format!("{}", self)
    }

    #[cfg(feature = "pyo3")]
    pub fn __repr__(&self) -> String {
        format!("{}", self)
    }

    pub fn is_expanded(&self) -> bool {
        !self.associated.is_empty()
    }

    pub fn expansion_count(&self) -> usize {
        self.associated.len()
    }

    pub fn total_len(&self) -> usize {
        self.root.len() + self.associated.iter().map(|(_, p)| p.len()).sum::<usize>()
    }
}

impl DecomposedPrimes {
    pub fn associated(&self) -> &HashMap<Variable, Primes> {
        &self.associated
    }
    pub fn root(&self) -> &Primes {
        &self.root
    }
}

impl DecompositionTracker {
    fn pick_var(&mut self) -> Variable {
        while self.variables.contains(self.next_var) {
            self.next_var.0 += 1;
        }

        let result = self.next_var;
        self.next_var.0 += 1;
        result
    }

    fn report(&self) -> DecomposeReport {
        DecomposeReport {
            root_score: self.score,
            sum_sub_score: self.expansion_score,
        }
    }
}

#[cfg_attr(feature = "pyo3", pymethods)]
impl DecomposeReport {
    #[cfg(feature = "pyo3")]
    pub fn __str__(&self) -> String {
        format!("{:?}", self)
    }

    #[cfg(feature = "pyo3")]
    pub fn __repr__(&self) -> String {
        format!("{:?}", self)
    }

    pub fn root_score(&self) -> usize {
        self.root_score
    }
    pub fn sub_score(&self) -> usize {
        self.sum_sub_score
    }
}

impl Display for DecomposedExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.associated.is_empty() {
            return write!(f, "{}", &self.root);
        }

        let root_expr = &self.root;
        writeln!(f, "Expanded {}", root_expr)?;
        for (v, e) in self.associated.iter() {
            writeln!(f, "  {} <- {}", v, e)?;
        }

        Ok(())
    }
}

impl Display for DecomposedPrimes {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.associated.is_empty() {
            return write!(f, "{}", &self.root);
        }

        let root_expr = &self.root;
        write!(f, "[[Expanded\nRoot: \n{}", root_expr)?;
        for (v, e) in self.associated.iter() {
            write!(f, "\nAssociated {}:\n{}", v, e)?;
        }
        writeln!(f, "]]")
    }
}

impl From<&DecomposedExpr> for DecomposedPrimes {
    fn from(dexpr: &DecomposedExpr) -> Self {
        let root = Primes::from(&dexpr.root);
        let associated = dexpr
            .associated
            .iter()
            .map(|(v, e)| (*v, Primes::from(e)))
            .collect();
        Self { root, associated }
    }
}

impl From<&DecomposedPrimes> for DecomposedExpr {
    fn from(dprimes: &DecomposedPrimes) -> Self {
        let root = Expr::from(&dprimes.root);
        let associated = dprimes
            .associated
            .iter()
            .map(|(v, e)| (*v, Expr::from(e)))
            .collect();
        Self { root, associated }
    }
}

impl From<&Expr> for DecomposedPrimes {
    fn from(expr: &Expr) -> Self {
        let (dexpr, _) = expr.decompose(None);
        DecomposedPrimes::from(&dexpr)
    }
}
impl From<Expr> for DecomposedPrimes {
    fn from(expr: Expr) -> Self {
        let (dexpr, _) = expr.decompose(None);
        DecomposedPrimes::from(&dexpr)
    }
}

impl From<&Expr> for DecomposedExpr {
    fn from(expr: &Expr) -> Self {
        expr.decompose(None).0
    }
}
impl From<Expr> for DecomposedExpr {
    fn from(expr: Expr) -> Self {
        expr.decompose(None).0
    }
}

#[cfg(test)]
mod test {
    use crate::{BokitError, VarSpace, VariableParser};
    use std::ops::Not;

    #[test]
    fn test_cplx_analysis() -> Result<(), BokitError> {
        let mut variables = VarSpace::default();
        let e = variables
            .extend()
            .parse_expression("(A & B) | (C & (D | !E))")?;

        assert_eq!(e.estimate_complexity().score(), Some(3));

        Ok(())
    }

    #[test]
    fn hard_func() -> Result<(), BokitError> {
        let penalty = Some(10);
        let mut variables = VarSpace::default();
        let e = variables
            .extend()
            .parse_expression("(__0__ | __1__) & (__2__ | __3__) & (__4__ | __5__) & (__6__ & (__7__ | (__8__ | __9__) & (__0__ | __1__) & (__2__ | __3__) & (__4__ | __5__) & (__7__ | __10__) & (__11__ | __12__ | __13__) & (__14__ | __15__) & (__16__ | __17__) & (__18__ | __19__) & (__20__ | __21__) & (__10__ & __22__ & __23__ | __7__ & (!__6__ | !__7__))) | __24__ & (__25__ | (__0__ | __1__) & (__2__ | __3__) & (__4__ | __5__) & (__26__ | __27__) & (__28__ | __29__) & (__25__ | __30__) & (__31__ | __32__) & (__22__ & __30__ & __33__ | __25__ & (!__24__ | !__25__))) | __22__ & !(__10__ & __22__ & __23__ | __22__ & __30__ & __33__))")?;

        println!("{}", &e);

        println!("{:?}", e.clone().not().estimate_complexity());
        let (eexpr, _rep) = e.not().decompose(penalty);
        for (v, e) in eexpr.associated.iter() {
            println!(
                "{} -> {:?} ==> {} vs {:?} => {}",
                v,
                e.estimate_complexity(),
                e.decompose(penalty).0.is_expanded(),
                e.not().estimate_complexity(),
                e.not().decompose(penalty).0.is_expanded()
            );
        }

        Ok(())
    }
}
