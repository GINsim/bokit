//! Decompose complex rules into bite-sized sub-rules.
//!
//! Each sub-rule is associated to an implicit variable.
//! Decomposition can heavily reduce the complexity of some operations,
//! e.g. to formulate a constraint-solving problem based on (prime) implicants.
//!
//! Related work: tree decomposition in non-ground ASP programs
//! https://www.dbai.tuwien.ac.at/research/project/lpopt/thesis.pdf

use crate::expr::{Expr, ExprNode};
use crate::*;
use std::borrow::Cow;
use std::fmt::{Display, Formatter};
use std::ops::Not;

/// Explode complex expressions into a collection of related expressions
/// to reduce the global size of the implicant covering.
#[derive(Clone, Debug)]
#[cfg_attr(feature = "pyo3", pyclass(module = "bokit"))]
pub struct DecomposedExpr {
    expr: Expr,
    expansions: HashMap<Variable, Expr>,
}

struct DecompositionTracker {
    variables: VarSet,
    next_var: Variable,
    penalty: usize,
    expansion_score: usize,
    score: usize,
}

#[derive(Clone, Debug)]
#[cfg_attr(feature = "pyo3", pyclass(module = "bokit"))]
pub struct DecompositionReport {
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
        !self.expansions.is_empty()
    }

    pub fn expansion_count(&self) -> usize {
        self.expansions.len()
    }

    pub fn count_prime_implicants(&self) -> usize {
        let mut count = 0;
        count += Primes::from_expr(&self.expr).len();

        for (_v, e) in self.expansions.iter() {
            count += Primes::from_expr(e).len();
        }
        count
    }
}

impl DecomposedExpr {
    pub(crate) fn new(e: &Expr, penalty: usize) -> (Self, DecompositionReport) {
        let mut slf = Self {
            expr: e.clone(),
            expansions: HashMap::new(),
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
            slf.expr = expr;
        }

        (slf, tracker.report())
    }

    pub fn expansions(&self) -> &HashMap<Variable, Expr> {
        &self.expansions
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
        self.expansions.insert(var, extracted);
        if parent_bool {
            var.into()
        } else {
            var.not()
        }
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

    fn report(&self) -> DecompositionReport {
        DecompositionReport {
            root_score: self.score,
            sum_sub_score: self.expansion_score,
        }
    }
}

#[cfg_attr(feature = "pyo3", pymethods)]
impl DecompositionReport {
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
        if self.expansions.is_empty() {
            return write!(f, "{}", &self.expr);
        }

        let root_expr = &self.expr;
        writeln!(f, "Expanded {}", root_expr)?;
        for (v, e) in self.expansions.iter() {
            writeln!(f, "  {} <- {}", v, e)?;
        }

        Ok(())
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

        // let eexpr = e.simplify(penalty);
        // println!("{:?}", e.complexity_score());
        // println!("{}", eexpr);
        // println!("{}", eexpr.expansion_score);
        // for (v, e) in eexpr.expansions.iter() {
        //     println!("{} -> {:?}", v, e.complexity_score());
        // }
        // println!("{}", eexpr.count_prime_implicants());
        //
        // println!();
        println!();

        println!("{:?}", e.clone().not().estimate_complexity());
        let eexpr = e.not().decompose(penalty);
        println!("{} => {}", eexpr, eexpr.expansion_score);
        for (v, e) in eexpr.expansions.iter() {
            println!(
                "{} -> {:?} ==> {} vs {:?} => {}",
                v,
                e.estimate_complexity(),
                e.decompose(penalty).is_expanded(),
                e.not().estimate_complexity(),
                e.not().decompose(penalty).is_expanded()
            );
        }
        // println!("{}", eexpr.count_prime_implicants());

        Ok(())
    }
}
