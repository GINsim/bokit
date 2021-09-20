use crate::{Expr, ImplicantSet, Primes, State, VarSet, VariableCollection};
use std::fmt;
use std::fmt::Formatter;

/// Common API for all Boolean rules.
///
/// This trait defines the API to evaluate and display Boolean rules
pub trait Rule {
    /// Display the rule using the selected helper
    fn fmt_rule(&self, f: &mut fmt::Formatter, namer: &VariableCollection) -> fmt::Result;

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
    /// Defined as an expression
    Expr(Expr),
    /// Defined as a list of prime implicants
    Primes(Primes),
    /// Defined as a list of implicants, which may not be prime
    Implicants(ImplicantSet),
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
    fn fmt_rule(&self, f: &mut fmt::Formatter, namer: &VariableCollection) -> fmt::Result {
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
