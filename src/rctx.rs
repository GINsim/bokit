//! Explode complex rules into more manageable sub-rules.
//!
//! Sub-rules correspond to implicit variables

use crate::expr::{Expr, ExprNode};
use crate::*;
use std::borrow::Cow;
use std::cmp::max;
use std::fmt::{Display, Formatter};

/// Evaluate the complexity of unfolding implicants from an expression
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "pyo3", pyclass(module = "bokit"))]
pub struct ExprComplexity {
    score: Option<usize>,
    atoms: usize,
    depth: usize,
}

/// Explode complex expressions into a collection of related expressions
/// to reduce the global size of the implicant covering.
#[derive(Clone, Debug, Default)]
#[cfg_attr(feature = "pyo3", pyclass(module = "bokit"))]
pub struct ExprExpander {
    simplified_expr: Option<Expr>,
    variables: VarSet,
    next_var: Variable,
    expansions: HashMap<Variable, Expr>,
    penalty: usize,
}

#[cfg_attr(feature = "pyo3", pymethods)]
impl ExprComplexity {
    #[cfg(feature = "pyo3")]
    pub fn __str__(&self) -> String {
        format!("{:?}", self)
    }

    #[cfg(feature = "pyo3")]
    pub fn __repr__(&self) -> String {
        format!("{:?}", self)
    }

    pub fn score(&self) -> Option<usize> {
        self.score
    }
    pub fn atoms(&self) -> usize {
        self.atoms
    }
    pub fn depth(&self) -> usize {
        self.depth
    }
}

#[cfg_attr(feature = "pyo3", pymethods)]
impl ExprExpander {
    #[cfg(feature = "pyo3")]
    pub fn __str__(&self) -> String {
        format!("{}", self)
    }

    #[cfg(feature = "pyo3")]
    pub fn __repr__(&self) -> String {
        format!("{}", self)
    }

    pub fn is_expanded(&self) -> bool {
        self.simplified_expr.is_some()
    }
}

impl ExprComplexity {
    fn new(score: usize, atoms: usize) -> Self {
        Self {
            score: Some(score),
            depth: 1,
            atoms,
        }
    }

    /// Recursively estimate the complexity score, taking into account the parent negation.
    /// * A false value has no complexity
    /// * A single variable or a true value has a unitary complexity
    /// * A conjunction has a multiplicative complexity
    /// * A disjunction has an additive complexity
    fn from_expr(e: &Expr, parent_bool: bool) -> Self {
        let b = e.value && parent_bool;
        match &e.node {
            ExprNode::Variable(_v) => Self::new(1, 1),
            ExprNode::True => Self::new(b as usize, 0),
            ExprNode::Pattern(p) => {
                let atoms = p.additional_len();
                Self::new(if b { 1 } else { atoms }, atoms)
            }
            ExprNode::Operation(o, children) => {
                let mut c1 = Self::from_expr(&children.0, b);
                let c2 = Self::from_expr(&children.1, b);
                match (b, o) {
                    (true, Operator::And) | (false, Operator::Or) => c1.and(&c2),
                    (true, Operator::Or) | (false, Operator::And) => c1.or(&c2),
                };
                c1
            }
        }
    }

    fn and(&mut self, o: &ExprComplexity) {
        self.depth = 1 + max(self.depth, o.depth);
        self.atoms += o.atoms;
        self.score = match (self.score, o.score) {
            (Some(s1), Some(s2)) => s1.checked_mul(s2),
            _ => None,
        };
    }

    fn or(&mut self, o: &ExprComplexity) {
        self.depth = 1 + max(self.depth, o.depth);
        self.atoms += o.atoms;
        self.score = match (self.score, o.score) {
            (Some(s1), Some(s2)) => s1.checked_add(s2),
            _ => None,
        };
    }
}

impl ExprExpander {
    pub fn new(e: &Expr) -> Self {
        Self::with_opt_penalty(e, None)
    }

    pub fn with_opt_penalty(e: &Expr, penalty: Option<usize>) -> Self {
        Self::with_penalty(e, penalty.unwrap_or(500))
    }

    pub fn with_penalty(e: &Expr, penalty: usize) -> Self {
        let mut slf = Self {
            simplified_expr: None,
            variables: e.get_regulators(),
            next_var: Variable(0),
            expansions: HashMap::new(),
            penalty,
        };

        let (e, _score) = slf.explore(e, true);
        if let Cow::Owned(expr) = e {
            slf.simplified_expr = Some(expr);
        }

        slf
    }

    fn explore<'a>(&mut self, e: &'a Expr, parent_bool: bool) -> (Cow<'a, Expr>, usize) {
        let b = e.value && parent_bool;
        let fwd = Cow::Borrowed(e);
        match &e.node {
            ExprNode::Variable(_v) => (fwd, 1),
            ExprNode::True => (fwd, b as usize),
            ExprNode::Pattern(p) => (fwd, if b { 1 } else { p.additional_len() }),
            ExprNode::Operation(o, children) => {
                let (mut e1, mut s1) = self.explore(&children.0, b);
                let (mut e2, mut s2) = self.explore(&children.1, b);
                if (b && o == &Operator::Or) || (!b && o == &Operator::And) {
                    return (forward_expr(fwd, *o, b, e1, e2), s1 + s2);
                }

                if s1 > 1 && s2 > 1 {
                    let savings = (s1 - 1) * (s2 - 1);
                    if savings > self.penalty {
                        if s1 > s2 {
                            e1 = Cow::Owned(Expr::from(self.extract_sub_expression(e1)));
                            s1 = 1;
                        } else {
                            e2 = Cow::Owned(Expr::from(self.extract_sub_expression(e2)));
                            s2 = 1;
                        }
                    }
                }

                (forward_expr(fwd, *o, b, e1, e2), s1 * s2)
            }
        }
    }

    fn extract_sub_expression(&mut self, e: Cow<Expr>) -> Variable {
        let var = self.pick_var();
        self.expansions.insert(var, e.into_owned());
        var
    }

    fn pick_var(&mut self) -> Variable {
        while self.variables.contains(self.next_var) {
            self.next_var.0 += 1;
        }

        let result = self.next_var;
        self.next_var.0 += 1;
        result
    }
}

fn forward_expr<'a>(
    fwd: Cow<'a, Expr>,
    op: Operator,
    b: bool,
    e1: Cow<'a, Expr>,
    e2: Cow<'a, Expr>,
) -> Cow<'a, Expr> {
    if matches!((&e1, &e2), (Cow::Borrowed(_), Cow::Borrowed(_))) {
        return fwd;
    }

    let children = Arc::new((e1.into_owned(), e2.into_owned()));
    Cow::Owned(Expr {
        value: b,
        node: ExprNode::Operation(op, children),
    })
}

impl From<&Expr> for ExprComplexity {
    fn from(e: &Expr) -> Self {
        Self::from_expr(e, true)
    }
}

impl Display for ExprExpander {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.simplified_expr.is_none() && self.expansions.is_empty() {
            return write!(f, "No simplification");
        }

        let root_expr = self.simplified_expr.as_ref().unwrap();
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

    #[test]
    fn test_cplx_analysis() -> Result<(), BokitError> {
        let mut variables = VarSpace::default();
        let e = variables
            .extend()
            .parse_expression("(A & B) | (C & (D | !E))")?;

        assert_eq!(e.complexity_score().score(), Some(3));

        Ok(())
    }
}
