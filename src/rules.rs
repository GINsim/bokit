use crate::efmt::{ExprFormatter, InfixFormatter};
use crate::{Expr, Implicants, Primes, State, VarSet, VarSpace};
use std::borrow::Cow;
use std::fmt;

/// Common API for all Boolean rules.
///
/// This trait defines the API to evaluate and display Boolean rules
pub trait Rule {
    /// Display using the default infix formatter
    fn fmt_rule(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut infix = InfixFormatter::new(f);
        self.fmt_with(&mut infix)
    }

    /// Display using the default infix formatter
    fn fmt_named(&self, f: &mut fmt::Formatter, vs: &VarSpace) -> fmt::Result {
        let mut infix = InfixFormatter::named(f, vs);
        self.fmt_with(&mut infix)
    }

    /// Display the rule using the selected formatter
    fn fmt_with(&self, f: &mut dyn ExprFormatter) -> fmt::Result;

    /// Evaluate the rule on the given state
    fn eval(&self, state: &State) -> bool;

    /// Add all regulators to the set of variables
    fn collect_regulators(&self, regulators: &mut VarSet);

    /// Construct the set of regulators
    fn get_regulators(&self) -> VarSet {
        let mut regulators = VarSet::default();
        self.collect_regulators(&mut regulators);
        regulators
    }

    /// Borrow or convert the rule as an expression
    fn as_expression(&self) -> Cow<Expr>;

    /// Borrow or convert the rule as an implicant cover
    fn as_implicants(&self) -> Cow<Implicants>;

    /// Borrow or convert the rule as a set of prime implicants
    fn as_primes(&self) -> Cow<Primes>;
}
