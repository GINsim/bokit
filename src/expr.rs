//! Boolean rules defined as expression trees

use core::ops::BitAnd;
use core::ops::BitOr;
use core::ops::Not;
use std::fmt;

use crate::parse::parse_expression;
use crate::*;
use once_cell::sync::Lazy;
use std::fmt::Debug;
use std::str::FromStr;

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
#[derive(Clone, PartialEq, Debug)]
pub enum Expr {
    /// A simple Boolean (true/false) expression
    Bool(bool),
    /// A variable literal
    Atom(Variable),
    /// A negated expression
    Not(Arc<Expr>),
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
    fn into_join(self, e: Expr, o: Operator) -> Self {
        match (&self, o, &e) {
            (Expr::Bool(true), Operator::And, _) => e,
            (Expr::Bool(false), Operator::And, _) => self,
            (Expr::Bool(true), Operator::Or, _) => self,
            (Expr::Bool(false), Operator::Or, _) => e,

            (_, Operator::And, Expr::Bool(true)) => self,
            (_, Operator::And, Expr::Bool(false)) => e,
            (_, Operator::Or, Expr::Bool(true)) => e,
            (_, Operator::Or, Expr::Bool(false)) => self,

            _ => Expr::Operation(o, Arc::new((self, e))),
        }
    }

    /// Clean formatting of expressions.
    ///
    /// This recursive function carries two additional arguments:
    /// * the priority of the parent to decide when to add parenthesis,
    /// * a closure to format atoms, enabling to switch from generic names to search in a custom data structure.
    fn _fmt_expr(
        &self,
        f: &mut fmt::Formatter,
        p: u8,
        namer: Option<&VariableCollection>,
    ) -> fmt::Result {
        match self {
            Expr::Bool(true) => write!(f, "True"),
            Expr::Bool(false) => write!(f, "False"),
            Expr::Atom(v) => match namer {
                Some(n) => n.format_variable(f, *v),
                None => v.fmt(f),
            },
            Expr::Not(e) => {
                write!(f, "!")?;
                e._fmt_expr(f, u8::MAX, namer)
            }
            Expr::Operation(o, c) => {
                let np = o.priority();
                if np < p {
                    write!(f, "(")?;
                }

                c.0._fmt_expr(f, np, namer)?;
                write!(f, " {} ", o)?;
                c.1._fmt_expr(f, np, namer)?;

                if np < p {
                    write!(f, ")")
                } else {
                    write!(f, "")
                }
            }
        }
    }

    fn _eval(&self, state: &State, positive: bool) -> bool {
        match self {
            Expr::Bool(b) => *b == positive,
            Expr::Not(e) => e._eval(state, !positive),
            Expr::Atom(var) => positive == state.is_active(*var),
            Expr::Operation(op, children) => {
                let b1 = children.0._eval(state, positive);
                let b2 = Lazy::new(|| children.1._eval(state, positive));
                match (positive, op) {
                    (true, Operator::And) => b1 && *b2,
                    (true, Operator::Or) => b1 || *b2,
                    (false, Operator::And) => b1 || *b2,
                    (false, Operator::Or) => b1 && *b2,
                }
            }
        }
    }
}

impl Operator {
    /// Define the priority of operators
    ///
    /// This priority controls the addition of necessary parenthesis when formatting expressions.
    fn priority(self) -> u8 {
        match self {
            Operator::And => 2,
            Operator::Or => 1,
        }
    }
}

impl FromStr for Expr {
    type Err = BokitError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parse_expression(&mut Variable::from_str, s)
    }
}

impl From<&Expr> for Expr {
    fn from(e: &Expr) -> Self {
        e.clone()
    }
}

impl From<bool> for Expr {
    fn from(b: bool) -> Self {
        Expr::Bool(b)
    }
}

impl<T: VariableID> From<T> for Expr {
    fn from(u: T) -> Self {
        Expr::Atom(Variable::from(u.uid()))
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
    fn fmt_rule(&self, f: &mut fmt::Formatter, namer: &VariableCollection) -> fmt::Result {
        self._fmt_expr(f, 0, Some(namer))
    }

    fn eval(&self, state: &State) -> bool {
        self._eval(state, true)
    }

    fn collect_regulators(&self, regulators: &mut VarSet) {
        match self {
            Expr::Bool(_) => (),
            Expr::Atom(v) => regulators.insert(*v),
            Expr::Not(e) => e.collect_regulators(regulators),
            Expr::Operation(_, children) => {
                children.0.collect_regulators(regulators);
                children.1.collect_regulators(regulators);
            }
        }
    }
}

// delegate Display impl to the Rule trait
impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self._fmt_expr(f, 0, None)
    }
}

/* ************************************************************************************* */
/* ******************************   Operator overloading  ****************************** */
/* ************************************************************************************* */

impl Not for Expr {
    type Output = Self;
    fn not(self) -> Self::Output {
        match self {
            Expr::Bool(b) => Expr::Bool(!b),
            Expr::Not(e) => Expr::from(e),
            _ => Expr::Not(Arc::new(self.clone())),
        }
    }
}

impl Not for &Expr {
    type Output = Expr;
    fn not(self) -> Self::Output {
        match self {
            Expr::Bool(b) => Expr::Bool(!*b),
            Expr::Not(e) => Expr::clone(e),
            _ => Expr::Not(Arc::new(self.clone())),
        }
    }
}

impl Not for Variable {
    type Output = Expr;
    fn not(self) -> Self::Output {
        !Expr::from(self)
    }
}

impl<T: Into<Expr>> BitAnd<T> for Expr {
    type Output = Expr;
    fn bitand(self, rhs: T) -> Self::Output {
        self.into_join(rhs.into(), Operator::And)
    }
}

impl<T: Into<Expr>> BitAnd<T> for &Expr {
    type Output = Expr;
    fn bitand(self, rhs: T) -> Self::Output {
        Expr::from(self).into_join(rhs.into(), Operator::And)
    }
}

impl<T: Into<Expr>> BitAnd<T> for Variable {
    type Output = Expr;
    fn bitand(self, rhs: T) -> Self::Output {
        Expr::from(self).into_join(rhs.into(), Operator::And)
    }
}

impl<T: Into<Expr>> BitOr<T> for Expr {
    type Output = Self;
    fn bitor(self, rhs: T) -> Self::Output {
        self.into_join(rhs.into(), Operator::Or)
    }
}

impl<T: Into<Expr>> BitOr<T> for &Expr {
    type Output = Expr;
    fn bitor(self, rhs: T) -> Self::Output {
        Expr::from(self).into_join(rhs.into(), Operator::Or)
    }
}

impl<T: Into<Expr>> BitOr<T> for Variable {
    type Output = Expr;
    fn bitor(self, rhs: T) -> Self::Output {
        Expr::from(self).into_join(rhs.into(), Operator::Or)
    }
}

#[cfg(test)]
mod tests {

    use crate::*;

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

        let mut variables = VariableCollection::default();
        let test = variables.add("test")?;
        let other = variables.add("other")?;
        let myvar = variables.add("myvar")?;

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
        let mut variables = VariableCollection::default();
        let v1 = variables.add("A")?;
        let v2 = variables.add("B")?;
        let v3 = variables.add("C")?;
        let v4 = variables.add("D")?;
        let v5 = variables.add("E")?;

        let e = variables.parse_expression("(A & B) | (C & (D | !E))")?;
        let e2 = (v1 & v2) | (v3 & (v4 | !v5));

        assert_eq!(e, e2);

        let mut variables = VariableCollection::default();
        let _e = variables.parse_expression_with_new_variables("(first & test) | other")?;

        let first = variables.add("first")?;
        let test = variables.add("test")?;
        let other = variables.add("other")?;
        let myvar = variables.add("myvar")?;

        let e: Expr = (test | other) & true & ((!myvar | first) & test);

        assert_eq!(false, e.eval(&variables.get_state("other")?));
        assert_eq!(true, e.eval(&variables.get_state("test")?));
        assert_eq!(false, e.eval(&variables.get_state("myvar test")?));
        assert_eq!(true, e.eval(&variables.get_state("myvar test first")?));

        Ok(())
    }
}
