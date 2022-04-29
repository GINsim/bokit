//! Explode complex rules into more manageable sub-rules.
//!
//! Sub-rules correspond to implicit variables

use crate::expr::ExprNode;
use crate::*;
use std::cmp::max;

static THRESHOLD: u64 = 10;

/// Evaluate the complexity of unfolding implicants from an expression
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "pyo3", pyclass(module = "bokit"))]
pub struct CplxInfo {
    score: u64,
    simpl: u64,
    depth: u32,
    atoms: u32,
}

#[derive(Default)]
struct SimplifyTracker {
    path: Vec<bool>,
}

#[cfg_attr(feature = "pyo3", pymethods)]
impl CplxInfo {
    #[cfg(feature = "pyo3")]
    pub fn __str__(&self) -> String {
        format!("{:?}", self)
    }

    #[cfg(feature = "pyo3")]
    pub fn __repr__(&self) -> String {
        format!("{:?}", self)
    }
}

impl CplxInfo {
    fn from_literal(_var: &Variable, _b: bool) -> Self {
        Self {
            score: 1,
            simpl: 1,
            depth: 1,
            atoms: 1,
        }
    }

    fn from_bool(b: bool) -> Self {
        let score = if b { 1 } else { 0 };
        Self {
            score,
            simpl: score,
            depth: 1,
            atoms: 0,
        }
    }

    fn from_pattern(p: &Pattern, b: bool) -> Self {
        let atoms = p.additional_len();
        let score = if b { 1 } else { atoms as u64 };

        Self {
            score,
            simpl: score,
            depth: 1,
            atoms: atoms as u32,
        }
    }

    /// Recursively estimate the complexity score, taking into account the parent negation.
    /// * A false value has no complexity
    /// * A single variable or a true value has a unitary complexity
    /// * A conjunction has a multiplicative complexity
    /// * A disjunction has an additive complexity
    fn from_expr(tracker: &mut SimplifyTracker, e: &Expr, parent_bool: bool) -> Self {
        let b = e.value && parent_bool;
        match &e.node {
            ExprNode::Variable(v) => CplxInfo::from_literal(v, b),
            ExprNode::True => CplxInfo::from_bool(b),
            ExprNode::Pattern(p) => CplxInfo::from_pattern(p, b),
            ExprNode::Operation(o, children) => {
                let mut c1 = Self::from_expr(tracker.visit_left(), &children.0, b);
                let c2 = Self::from_expr(tracker.visit_right(), &children.1, b);
                match (b, o) {
                    (true, Operator::And) | (false, Operator::Or) => c1.and(tracker, &c2),
                    (true, Operator::Or) | (false, Operator::And) => c1.or(&c2),
                };
                tracker.backtrack();
                c1
            }
        }
    }

    fn and(&mut self, _tracker: &mut SimplifyTracker, o: &CplxInfo) {
        let score = self.score * o.score;
        let simpl = self.simpl * o.simpl;

        if simpl > THRESHOLD {
            // We should simplify here!
            println!("Found a simplification candidate");
        }

        self.score *= score;
        self.simpl = simpl;
        self.depth = 1 + max(self.depth, o.depth);
        self.atoms += o.atoms;
    }

    fn or(&mut self, o: &CplxInfo) {
        self.score += o.score;
        self.simpl += o.simpl;
        self.depth = 1 + max(self.depth, o.depth);
        self.atoms += o.atoms;
    }
}

impl SimplifyTracker {
    fn new() -> Self {
        Self { path: Vec::new() }
    }

    fn visit_left(&mut self) -> &mut Self {
        self.path.push(false);
        self
    }

    fn visit_right(&mut self) -> &mut Self {
        *self.path.last_mut().unwrap() = true;
        self
    }

    fn backtrack(&mut self) {
        self.path.pop();
    }
}

impl From<&Expr> for CplxInfo {
    fn from(e: &Expr) -> Self {
        let mut tracker = SimplifyTracker::new();
        Self::from_expr(&mut tracker, e, true)
    }
}
