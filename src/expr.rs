//! Boolean rules defined as expression trees

use core::ops::BitAnd;
use core::ops::BitOr;
use core::ops::Not;
use std::borrow::{Borrow, Cow};
use std::fmt::Debug;
use std::str::FromStr;

use crate::parse::VariableParser;
use crate::*;

#[cfg(feature = "pyo3")]
use pyo3::exceptions::PyValueError;

/// A Boolean expression tree.
///
/// Represents a Boolean rule as a tree where internal nodes are classical Boolean operations
/// and leaves are individual variables (or fixed Boolean values).
/// Expressions overload the ```&```, ```|```, and ```!``` operators to facilitate their definition
/// as readable rust statements. Fixed Boolean values and double negations are eliminated.
///
/// Expressions can not be [copied](Copy) but they can be [cloned](Clone) in constant time.
///
/// ```
/// use bokit::{Expr, Rule, State,Variable};
/// # use bokit::BokitError;
/// # fn main() -> Result<(), BokitError> {
///
/// // Create some variables
/// use std::os::linux::raw::stat;
/// let a = Variable::from(0);
/// let b = Variable::from(1);
/// let c = Variable::from(2);
///
/// // Build expressions using these variables
/// let sub_expr = b & !c;
/// let pos_expr = a & !sub_expr;
/// let neg_expr = !&pos_expr;
///
/// // Evaluate expressions on some state
/// let state: State = "011".parse()?;
/// assert_ne!(pos_expr.eval(&state), neg_expr.eval(&state));
/// # Ok(())
/// # }
/// ```
///
/// # Parsing expressions
///
/// An expression can be parsed from a string where
/// ```|```, ```&``` and ```!``` denote the ```OR```, ```AND``` and ```NOT``` Boolean operators
/// and variables are identified by UID enclosed between underline characters (```_```).
///
/// ```
/// use bokit::Expr;
/// # use bokit::BokitError;
/// # fn main() -> Result<(), BokitError> {
///
/// let expr: Expr = "_0_ & !(_1_ & !_2_)".parse()?;
/// # Ok(())
/// # }
/// ```
#[cfg_attr(feature = "pyo3", pyclass(module = "bokit"))]
#[derive(Clone, PartialEq, Debug)]
pub struct Expr {
    pub(crate) value: bool,
    pub(crate) node: ExprNode,
}

/// A node in an expression tree
#[derive(Clone, PartialEq, Debug)]
pub(crate) enum ExprNode {
    /// A fixed Boolean value
    True,

    /// A single literal
    Variable(Variable),

    /// A pattern
    Pattern(Pattern),

    /// Two expressions connected with a binary operator
    Operation(Operator, Arc<(Expr, Expr)>),
}

#[derive(Copy, Clone, PartialEq, Debug)]
/// Expression trees can use the AND and OR operators.
pub enum Operator {
    /// AND operator: both children need to be true
    And,
    /// OR operator: at least one child needs to be true
    Or,
}

impl Expr {
    fn new(value: bool, node: ExprNode) -> Self {
        Self { value, node }
    }

    fn _fmt_expr(&self, f: &mut dyn efmt::ExprFormatter, parent: Option<Operator>) -> fmt::Result {
        match &self.node {
            ExprNode::True => f.write_bool(self.value),
            ExprNode::Variable(var) => f.write_variable(*var, self.value),
            ExprNode::Pattern(p) => f.write_pattern(p, self.value, parent),
            ExprNode::Operation(o, c) => {
                f.start_operation(*o, self.value, parent)?;
                c.0._fmt_expr(f, Some(*o))?;
                f.sep_operation(*o)?;
                c.1._fmt_expr(f, Some(*o))?;
                f.end_operation(*o, self.value, parent)
            }
        }
    }

    /// Rewrite an expression by replacing some variables with new expressions.
    ///
    /// The function will call the closure on all variables in the expression.
    /// The closure takes two arguments: the variable itself and a flag indicating
    /// if the expression is positive or negative in the global context.
    /// If the closure returns None, then the variable is unchanged, otherwise it a new expression
    /// is used to reconstruct the expression tree.
    ///
    /// If the expression is unchanged, only the root node will be duplicated, the necessary subtrees
    /// are reconstructed and the original expression remains unchanged.
    ///
    /// This function is used to implement the restriction of an expression into a subspace,
    /// but can be used for other rewriting operations. In most cases it should not be used directly.
    pub(crate) fn rewrite_cow<FV, FP>(&self, fv: &FV, fp: &FP) -> Self
    where
        FV: Fn(Variable, bool) -> Option<Expr>,
        FP: Fn(&Pattern, bool) -> Option<Expr>,
    {
        self._rewrite_cow(fv, fp, true).into_owned()
    }

    fn _rewrite_cow<FV, FP>(&self, fv: &FV, fp: &FP, value: bool) -> Cow<Self>
    where
        FV: Fn(Variable, bool) -> Option<Expr>,
        FP: Fn(&Pattern, bool) -> Option<Expr>,
    {
        match &self.node {
            ExprNode::True => Cow::Borrowed(self),
            ExprNode::Variable(var) => match fv(*var, value == self.value) {
                None => Cow::Borrowed(self),
                Some(e) => Cow::Owned(e),
            },
            ExprNode::Pattern(p) => match fp(p, self.value == value) {
                None => Cow::Borrowed(self),
                Some(e) => match self.value {
                    true => Cow::Owned(e),
                    false => Cow::Owned(!e),
                },
            },
            ExprNode::Operation(op, children) => {
                let c1 = children.0._rewrite_cow(fv, fp, value == self.value);
                let c2 = children.1._rewrite_cow(fv, fp, value == self.value);
                if let (Cow::Borrowed(_), Cow::Borrowed(_)) = (&c1, &c2) {
                    return Cow::Borrowed(self);
                }
                Cow::Owned(op.join_with_value(self.value, c1.into_owned(), c2.into_owned()))
            }
        }
    }

    pub fn _complexity_score(&self, parent_bool: bool) -> usize {
        let b = self.value && parent_bool;
        match &self.node {
            ExprNode::Variable(_) => 1,
            ExprNode::True => {
                match b {
                    true => 1,
                    false => 0,
                }
            },
            ExprNode::Pattern(p) => match b {
                true => 1,
                false => p.additional_len(),
            },
            ExprNode::Operation(o, children) => {
                let c1 = children.0._complexity_score(b);
                let c2 = children.1._complexity_score(b);
                match (b, o) {
                    (true, Operator::And) => c1 * c2,
                    (false, Operator::Or) => c1 * c2,
                    (true, Operator::Or) => c1 + c2,
                    (false, Operator::And) => c1 + c2,
                }
            },
        }
    }
}

#[cfg_attr(feature = "pyo3", pymethods)]
impl Expr {
    #[cfg(feature = "pyo3")]
    #[new]
    fn new_py(arg: Option<&PyAny>) -> PyResult<Self> {
        match arg {
            None => Ok(Expr::from(false)),
            Some(obj) => extract_expr(obj),
        }
    }

    #[cfg(feature = "pyo3")]
    #[pyo3(name = "eval")]
    fn eval_py(&self, state: &State) -> bool {
        self.eval(state)
    }

    /// Restrict the function in a subspace: replace the fixed variables by their value
    ///
    /// Free variables are unaffected, fixed variables are replaced by their value.
    /// For consistency with the [restriction of lists of implicants](Implicants::restrict_to_subspace),
    /// conflicting variables are replaced with the negated flag obtained from their parent tree.
    /// The resulting function is true if it can be true for any value of the conflicting variables.
    pub fn restrict_to_subspace(&self, subspace: &Pattern) -> Self {
        let mut conflicts = subspace.positive.clone();
        conflicts.retain_set(&subspace.negative);
        self.rewrite_cow(&|v, b| subspace.restrict_variable(v, b), &|p, b| {
            p.restrict_with_conflicts(subspace, &conflicts, b)
        })
    }

    /// Estimated computational complexity of the expression.
    /// This computes the maximal number of prime implicants needed
    /// to cover this expression.
    /// This estimate can be completely off when sub-expressions share some variables, but it
    /// gives a reliable upper-bound.
    pub fn complexity_score(&self) -> usize {
        self._complexity_score(true)
    }

    #[cfg(feature = "pyo3")]
    pub fn __str__(&self) -> String {
        format!("{}", self)
    }

    #[cfg(feature = "pyo3")]
    pub fn __repr__(&self) -> String {
        format!("{}", self)
    }

    #[cfg(feature = "pyo3")]
    pub fn __or__(&self, rhs: &PyAny) -> PyResult<Expr> {
        Ok(self | extract_expr(rhs)?)
    }

    #[cfg(feature = "pyo3")]
    pub fn __and__(&self, rhs: &PyAny) -> PyResult<Expr> {
        Ok(self & extract_expr(rhs)?)
    }

    #[cfg(feature = "pyo3")]
    pub fn __invert__(&self) -> Expr {
        self.not()
    }
}

#[cfg(feature = "pyo3")]
fn extract_expr(obj: &PyAny) -> PyResult<Expr> {
    if let Ok(e) = obj.extract::<'_, Expr>() {
        return Ok(e);
    }
    if let Ok(e) = obj.extract::<'_, Variable>() {
        return Ok(Expr::from(e));
    }
    if let Ok(e) = obj.extract::<'_, Pattern>() {
        return Ok(Expr::from(e));
    }
    if let Ok(e) = obj.extract::<'_, Implicants>() {
        return Ok(Expr::from(&e));
    }
    if let Ok(e) = obj.extract::<'_, Primes>() {
        return Ok(Expr::from(&e));
    }
    if let Ok(e) = obj.extract::<'_, bool>() {
        return Ok(Expr::from(e));
    }
    if let Ok(e) = obj.extract::<'_, &str>() {
        return Ok(Expr::from_str(e)?);
    }
    Err(PyValueError::new_err(format!(
        "'{}' cannot be converted to 'Expr'",
        obj.get_type().name()?
    )))
}

impl Operator {
    /// Define the priority of operators
    ///
    /// This priority controls the addition of necessary parenthesis when formatting expressions.
    pub fn priority(self) -> u8 {
        match self {
            Operator::And => 2,
            Operator::Or => 1,
        }
    }

    fn join_with_value(
        self,
        value: bool,
        e1: impl Borrow<Expr> + Into<Expr>,
        e2: impl Borrow<Expr> + Into<Expr>,
    ) -> Expr {
        match value {
            true => self.join(e1, e2),
            false => self.join(e1, e2).not(),
        }
    }

    fn join(self, e1: impl Borrow<Expr> + Into<Expr>, e2: impl Borrow<Expr> + Into<Expr>) -> Expr {
        let (b1, b2) = (e1.borrow(), e2.borrow());
        match (&b1.node, &b2.node) {
            (ExprNode::True, _) => self.fixed_or(b1.value, e2),
            (_, ExprNode::True) => self.fixed_or(b2.value, e1),
            (ExprNode::Variable(v1), ExprNode::Variable(v2)) => {
                self.join_variables(*v1, b1.value, *v2, b2.value)
            }
            (ExprNode::Pattern(p), ExprNode::Variable(v)) => {
                match self.try_extend_pattern(p, b1.value, *v, b2.value) {
                    Err(_) => self._force_join(e1, e2),
                    Ok(None) => e1.into(),
                    Ok(Some(e)) => e,
                }
            }
            (ExprNode::Variable(v), ExprNode::Pattern(p)) => {
                match self.try_extend_pattern(p, b2.value, *v, b1.value) {
                    Err(_) => self._force_join(e1, e2),
                    Ok(None) => e2.into(),
                    Ok(Some(e)) => e,
                }
            }
            _ => self._force_join(e1, e2),
        }
    }

    fn try_extend_pattern(
        &self,
        pattern: &Pattern,
        v_pattern: bool,
        var: Variable,
        v_var: bool,
    ) -> Result<Option<Expr>, ()> {
        match (self, v_pattern) {
            (Operator::And, false) => Err(()),
            (Operator::Or, true) => Err(()),
            _ => {
                match (
                    pattern.is_fixed_at(var, v_var == v_pattern),
                    pattern.is_fixed_at(var, v_var != v_pattern),
                ) {
                    (_, true) => Ok(Some((!v_pattern).into())),
                    (true, false) => Ok(None),
                    (false, false) => {
                        let mut result = pattern.clone();
                        result.set_ignoring_conflicts(var, v_var == v_pattern);
                        Ok(Some(Expr::new(v_pattern, ExprNode::Pattern(result))))
                    }
                }
            }
        }
    }

    fn join_variables(self, v1: Variable, b1: bool, v2: Variable, b2: bool) -> Expr {
        if v1 == v2 {
            return match (self, b1, b2) {
                (_, true, true) => v1.into(),
                (_, false, false) => !v1,
                (Operator::And, _, _) => false.into(),
                (Operator::Or, _, _) => true.into(),
            };
        }

        let mut pattern = Pattern::default();
        pattern.set_ignoring_conflicts(v1, b1);
        pattern.set_ignoring_conflicts(v2, b2);
        match self {
            Operator::And => pattern.into(),
            Operator::Or => {
                pattern.negate_all_variables();
                !pattern
            }
        }
    }

    fn _force_join(self, e1: impl Into<Expr>, e2: impl Into<Expr>) -> Expr {
        Expr::from(ExprNode::Operation(self, Arc::new((e1.into(), e2.into()))))
    }

    fn is_fixed_by(self, b: bool) -> bool {
        match (self, b) {
            (Operator::And, false) => true,
            (Operator::Or, true) => true,
            (Operator::And, true) => false,
            (Operator::Or, false) => false,
        }
    }

    fn fixed_or(self, b: bool, e: impl Into<Expr>) -> Expr {
        match self.is_fixed_by(b) {
            true => Expr::from(b),
            false => e.into(),
        }
    }
}

impl FromStr for Expr {
    type Err = BokitError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parse::parser().parse_expression(s)
    }
}

impl From<&Expr> for Expr {
    fn from(e: &Expr) -> Self {
        e.clone()
    }
}

impl From<ExprNode> for Expr {
    fn from(node: ExprNode) -> Self {
        Self::new(true, node)
    }
}

impl From<bool> for Expr {
    fn from(b: bool) -> Self {
        Self::new(b, ExprNode::True)
    }
}

impl From<Variable> for Expr {
    fn from(var: Variable) -> Self {
        Self::from(ExprNode::Variable(var))
    }
}

impl From<Pattern> for Expr {
    fn from(p: Pattern) -> Self {
        if p.is_free_pattern() {
            return true.into();
        }
        if p.has_conflict() {
            return false.into();
        }
        match (p.positive.len(), p.negative.len()) {
            (0, 0) => true.into(),
            (1, 0) => p.positive.iter().next().unwrap().into(),
            (0, 1) => p.negative.iter().next().unwrap().into(),
            _ => Self::from(ExprNode::Pattern(p)),
        }
    }
}

impl From<Arc<Expr>> for Expr {
    fn from(r: Arc<Expr>) -> Self {
        match Arc::<Expr>::try_unwrap(r) {
            Ok(e) => e,
            Err(r) => Expr::clone(&r),
        }
    }
}

impl fmt::Display for Operator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Operator::And => write!(f, "&"),
            Operator::Or => write!(f, "|"),
        }
    }
}

impl Rule for Expr {
    fn fmt_with(&self, f: &mut dyn efmt::ExprFormatter) -> fmt::Result {
        self._fmt_expr(f, None)
    }

    fn eval(&self, state: &State) -> bool {
        self.value
            == match &self.node {
                ExprNode::True => true,
                ExprNode::Variable(var) => state.is_active(*var),
                ExprNode::Pattern(p) => p.contains_state(state),
                ExprNode::Operation(op, children) => match (op, children.0.eval(state)) {
                    (Operator::And, false) => false,
                    (Operator::Or, true) => true,
                    _ => children.1.eval(state),
                },
            }
    }

    fn collect_regulators(&self, regulators: &mut VarSet) {
        match &self.node {
            ExprNode::True => (),
            ExprNode::Variable(var) => regulators.insert(*var),
            ExprNode::Pattern(p) => {
                regulators.insert_set(&p.positive);
                regulators.insert_set(&p.negative);
            }
            ExprNode::Operation(_, children) => {
                children.0.collect_regulators(regulators);
                children.1.collect_regulators(regulators);
            }
        }
    }
}

// Delegate Display to the rule trait
impl fmt::Display for Expr {
    fn fmt<'a>(&self, f: &'a mut fmt::Formatter<'_>) -> fmt::Result {
        Rule::fmt_rule(self, f)
    }
}

/* ************************************************************************************* */
/* ******************************   Operator overloading  ****************************** */
/* ************************************************************************************* */

impl Not for Expr {
    type Output = Self;
    fn not(self) -> Self::Output {
        Self::new(!self.value, self.node)
    }
}

impl Not for &Expr {
    type Output = Expr;
    fn not(self) -> Self::Output {
        Expr::new(!self.value, self.node.clone())
    }
}

impl<T: Into<Expr>> BitAnd<T> for Expr {
    type Output = Expr;
    fn bitand(self, rhs: T) -> Self::Output {
        Operator::And.join(self, rhs.into())
    }
}

impl<T: Into<Expr>> BitAnd<T> for &Expr {
    type Output = Expr;
    fn bitand(self, rhs: T) -> Self::Output {
        Operator::And.join(self, rhs.into())
    }
}

impl<T: Into<Expr>> BitAnd<T> for Variable {
    type Output = Expr;
    fn bitand(self, rhs: T) -> Self::Output {
        Operator::And.join(Expr::from(self), rhs.into())
    }
}

impl<T: Into<Expr>> BitOr<T> for Expr {
    type Output = Self;
    fn bitor(self, rhs: T) -> Self::Output {
        Operator::Or.join(self, rhs.into())
    }
}

impl<T: Into<Expr>> BitOr<T> for &Expr {
    type Output = Expr;
    fn bitor(self, rhs: T) -> Self::Output {
        Operator::Or.join(self, rhs.into())
    }
}

impl<T: Into<Expr>> BitOr<T> for Variable {
    type Output = Expr;
    fn bitor(self, rhs: T) -> Self::Output {
        Operator::Or.join(Expr::from(self), rhs.into())
    }
}

#[cfg(test)]
mod tests {

    use crate::{parse::VariableParser, *};

    #[test]
    fn construct_and_display() -> Result<(), BokitError> {
        let a = Variable::from(1);
        let b = Variable::from(2);

        let t = Expr::from(true);
        let f = Expr::from(false);

        let expr = !(a | b);

        let c_expr = &f | &expr;

        println!("{}", &c_expr);

        let e = a | (b & &t);
        println!("{}", &e);

        let e = a & (b | &t);
        println!("{}", &e);

        let mut variables = VarSpace::default();
        let test = variables.provide("test")?;
        let other = variables.provide("other")?;
        let myvar = variables.provide("myvar")?;

        let e: Expr = (test | other) & true & (!myvar & test);
        println!();
        println!("{}", &e);
        println!("{}", variables.named(&e));

        println!();
        println!("{}", &c_expr);
        println!("{}", variables.named(&c_expr));

        Ok(())
    }

    #[test]
    fn eval() -> Result<(), BokitError> {
        let mut variables = VarSpace::default();
        let v1 = variables.provide("A")?;
        let v2 = variables.provide("B")?;
        let v3 = variables.provide("C")?;
        let v4 = variables.provide("D")?;
        let v5 = variables.provide("E")?;

        let e = variables.parse_expression("(A & B) | (C & (D | !E))")?;
        let e2 = (v1 & v2) | (v3 & (v4 | !v5));

        assert_eq!(e, e2);

        let mut variables = VarSpace::default();
        let _e = variables
            .extend()
            .parse_expression("(first & test) | other")?;

        let first = variables.provide("first")?;
        let test = variables.provide("test")?;
        let other = variables.provide("other")?;
        let myvar = variables.provide("myvar")?;

        let e: Expr = (test | other) & true & ((!myvar | first) & test);

        assert_eq!(false, e.eval(&variables.parse_state("other")?));
        assert_eq!(true, e.eval(&variables.parse_state("test")?));
        assert_eq!(false, e.eval(&variables.parse_state("myvar test")?));
        assert_eq!(true, e.eval(&variables.parse_state("myvar test first")?));

        Ok(())
    }

    #[test]
    fn restrict_subspace() -> Result<(), BokitError> {
        let mut vs = VarSpace::default();
        let e1 = vs.extend().parse_expression("A | !(B & C) | D")?;
        let e2 = vs.extend().parse_expression("A | (B & C)")?;
        let e3 = !&e2;

        let var_b = vs.get_or_err("B")?;
        let var_d = vs.get_or_err("D")?;

        let mut sub = Pattern::default();
        sub.set(var_d, false);
        assert_eq!(
            e1.restrict_to_subspace(&sub),
            vs.parse_expression("A | !(B & C)")?
        );
        assert_eq!(e2.restrict_to_subspace(&sub), e2.clone());

        sub.set(var_b, true);
        assert_eq!(
            e1.restrict_to_subspace(&sub),
            vs.parse_expression("A | !C")?
        );
        assert_eq!(e2.restrict_to_subspace(&sub), vs.parse_expression("A | C")?);

        sub.set(var_b, false);
        assert_eq!(e1.restrict_to_subspace(&sub), Expr::from(true));
        assert_eq!(e2.restrict_to_subspace(&sub), vs.parse_expression("A")?);
        assert_eq!(e3.restrict_to_subspace(&sub), vs.parse_expression("!A")?);

        sub.set_ignoring_conflicts(var_b, true);
        assert_eq!(
            e1.restrict_to_subspace(&sub),
            vs.parse_expression("A | !C")?
        );
        assert_eq!(e2.restrict_to_subspace(&sub), vs.parse_expression("A")?);
        assert_eq!(
            e3.restrict_to_subspace(&sub),
            vs.parse_expression("!A & !C")?
        );

        Ok(())
    }
}
