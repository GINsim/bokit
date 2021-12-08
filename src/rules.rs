use crate::{Expr, Implicants, Primes, State, VarSet, VarSpace};
use std::fmt;
use std::fmt::Formatter;

/// Common API for all Boolean rules.
///
/// This trait defines the API to evaluate and display Boolean rules
pub trait Rule {
    /// Display the rule using the selected helper
    fn fmt_rule(&self, f: &mut fmt::Formatter, namer: &VarSpace) -> fmt::Result;

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
}

/// A rule defined in one of the available data structure.
#[derive(Clone, Debug)]
pub enum SomeRule {
    /// List of implicants representing a DNF
    Implicants(Implicants),

    /// List of implicants guaranteed to be prime, also representing a DNF
    Primes(Primes),

    /// Expression tree in free form
    Expr(Expr),
}

impl SomeRule {
    fn inner_rule(&self) -> &dyn Rule {
        match self {
            SomeRule::Expr(e) => e,
            SomeRule::Implicants(i) => i,
            SomeRule::Primes(p) => p,
        }
    }
}

impl Rule for SomeRule {
    fn fmt_rule(&self, f: &mut fmt::Formatter, namer: &VarSpace) -> fmt::Result {
        self.inner_rule().fmt_rule(f, namer)
    }

    fn eval(&self, state: &State) -> bool {
        self.inner_rule().eval(state)
    }

    fn collect_regulators(&self, regulators: &mut VarSet) {
        self.inner_rule().collect_regulators(regulators)
    }
}

impl fmt::Display for SomeRule {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            SomeRule::Expr(v) => write!(f, "{}", v),
            SomeRule::Implicants(v) => write!(f, "{}", v),
            SomeRule::Primes(v) => write!(f, "{}", v),
        }
    }
}
