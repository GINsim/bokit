use crate::*;
use std::borrow::Cow;

use std::fmt;
use std::str::FromStr;

use crate::efmt::ExprFormatter;
use crate::variable::VariableCounter;
#[cfg(feature = "pyo3")]
use pyo3::prelude::*;
use std::ops::Not;

/// A subspace defined by sets of active and inactive variables, the others are implicitly free.
///
/// They are represented as a pair of [VarSet] to store positive and negative variables.
/// In a well-formed pattern, a variable should not be constrained to both values,
/// i.e. the intersection of both bitsets should be empty. However, some operations
/// on patterns do not prevent the creation of conflicts, either for performance reasons
/// or to use them to carry extra information.
///
/// It is defined as two sets (bit-sets again) of fixed variables, while other variables are implicitly free.
/// A Boolean rule could be true for some states of a pattern and false for others, so it cannot be used to
/// evaluate a rule.
///
/// A Pattern can be parsed from strings where the position in the string defines the
/// variable UID and the character defines the activation state: - for free, 0 for inactive, 1 for active.
/// To make the strings easier to read, spaces and single quotes are ignored around and inside the string.
/// For example "0-100-100", "  0-100-100", and "0-100 -100" are equivalent.
///
/// # Operations on patterns
///
/// Patterns provide many operations, based on bitwise operation when possible, notably:
/// * Test the inclusion of a state or another pattern
/// * Build the intersection of two patterns if it exists
/// * Identify emerging patterns (covered by two patterns but not included in any)
#[cfg_attr(feature = "pyo3", pyclass(module = "bokit"))]
#[derive(Clone, PartialEq, Eq, Default, Debug)]
pub struct Pattern {
    pub(crate) positive: VarSet,
    pub(crate) negative: VarSet,
}

impl Pattern {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a pattern from the two inner sets of fixed variables
    pub fn with(positive: VarSet, negative: VarSet) -> Self {
        Self { positive, negative }
    }

    /// Create a pattern restricted to a single state
    /// To properly set all variables fixed at 0, this requires
    /// an extra parameter giving the list of variables.
    pub fn from_state(state: State, variables: impl Into<VarSet>) -> Pattern {
        let mut neg = variables.into();
        let mut pos = state.into_active();
        pos.retain_set(&neg);
        neg.remove_set(&pos);
        Pattern::with(pos, neg)
    }

    /// Parse a pattern using the specified variables
    ///
    /// Instead of using naturally ordered variables as in the default parser,
    /// we provide an ordered list of variables used in the string representation
    pub fn parse_with_variables(descr: &str, variables: &VarList) -> Result<Self, BokitError> {
        let mut p = Pattern::default();
        let mut vars = variables.iter();
        for c in descr.chars() {
            match c {
                ' ' | '\t' | '\'' => (), // skip spacing and ` for formatting
                '-' => {
                    vars.next();
                }
                '0' => p
                    .negative
                    .insert(*vars.next().ok_or(BokitError::InvalidExpression)?),
                '1' => p
                    .positive
                    .insert(*vars.next().ok_or(BokitError::InvalidExpression)?),
                _ => return Err(BokitError::InvalidExpression),
            };
        }
        Ok(p)
    }

    pub(crate) fn restrict_with_conflicts(
        &self,
        subspace: &Pattern,
        conflicts: &VarSet,
        positive: bool,
    ) -> Option<Expr> {
        if self.has_fixed_variables(conflicts) {
            if positive {
                return Some(false.into());
            }

            // remove satisfied and conflicting variables
            let mut result = self.clone();
            result.free_set(conflicts);
            result.remove_shared_restrictions(subspace);
            return Some(result.into());
        }

        // false on conflicting variables
        if !self.positive.is_disjoint(&subspace.negative)
            || !self.negative.is_disjoint(&subspace.positive)
        {
            return Some(false.into());
        }

        // Unchanged in absence of satisfied variable
        if self.positive.is_disjoint(&subspace.positive)
            && self.negative.is_disjoint(&subspace.negative)
        {
            return None;
        }

        // Remove satisfied variables
        let mut result = self.clone();
        result.remove_shared_restrictions(subspace);
        Some(result.into())
    }

    pub(crate) fn restrict_variable<T: From<bool>>(
        &self,
        v: Variable,
        positive: bool,
    ) -> Option<T> {
        match (self.positive.contains(v), self.negative.contains(v)) {
            (false, false) => None,
            (true, false) => Some(true),
            (false, true) => Some(false),
            (true, true) => Some(!positive),
        }
        .map(|b| b.into())
    }

    pub fn iter_fixed_values(&self) -> impl Iterator<Item = (Variable, bool)> + '_ {
        self.positive
            .iter()
            .map(|v| (v, true))
            .chain(self.negative.iter().map(|v| (v, false)))
    }
}

#[cfg_attr(feature = "pyo3", pymethods)]
impl Pattern {
    #[cfg(feature = "pyo3")]
    #[new]
    fn new_py(s: Option<&str>) -> PyResult<Self> {
        Ok(match s {
            Some(descr) => Pattern::from_str(descr)?,
            None => Pattern::default(),
        })
    }

    /// Check if all variables are free in this pattern.
    ///
    /// returns true if the positive and negative sets are both empty
    pub fn is_free_pattern(&self) -> bool {
        self.positive.is_empty() && self.negative.is_empty()
    }

    /// Test if a variable is fixed at any value in this pattern
    pub fn is_fixed(&self, var: Variable) -> bool {
        self.positive.contains(var) || self.positive.contains(var)
    }

    /// Test if a variable is fixed at a specific value in this pattern
    pub fn is_fixed_at(&self, var: Variable, value: bool) -> bool {
        match value {
            true => self.positive.contains(var),
            false => self.negative.contains(var),
        }
    }

    /// Fix a variable to a specific value.
    ///
    /// If this variable was free, this leads to a restriction of the pattern.
    /// If it was fixed to the same value, the pattern is unchanged.
    /// If it was fixed to the opposite value, the existing restriction
    /// is replaced by the new one (giving a mirror pattern).
    pub fn set(&mut self, var: Variable, value: bool) {
        if value {
            self.negative.remove(var);
            self.positive.insert(var);
        } else {
            self.positive.remove(var);
            self.negative.insert(var);
        }
    }

    /// Fix a variable if it does not introduce a conflict.
    ///
    /// Returns true if the variable was free or already fixed at the required value.
    /// Returns false if the variable was previously fixed at the opposite value.
    pub fn try_set(&mut self, var: Variable, value: bool) -> bool {
        if self.is_fixed_at(var, !value) {
            return false;
        }
        self.set_ignoring_conflicts(var, value);
        true
    }

    /// Remove a single constraint.
    ///
    /// This removes a constraint fixing a variable at the specified value if it exists.
    /// If this constraint did not exist, nothing is changed.
    /// If the same variable had a conflict (was set at both values), the confliuct is lifted
    /// and the other constraint remains.
    pub fn unset(&mut self, var: Variable, value: bool) {
        if value {
            self.positive.remove(var);
        } else {
            self.negative.remove(var);
        }
    }

    /// Remove all constraints on a given variable.
    pub fn free_variable(&mut self, var: Variable) {
        self.positive.remove(var);
        self.negative.remove(var);
    }

    /// Remove all constraints on a set of variables.
    pub fn free_set(&mut self, vars: &VarSet) {
        self.positive.remove_set(vars);
        self.negative.remove_set(vars);
    }

    /// Remove restrictions shared with an other pattern.
    ///
    /// Note that this considers positive and negative restrictions separately and
    /// does not handle conflicts.
    pub fn remove_shared_restrictions(&mut self, subspace: &Pattern) {
        self.positive.remove_set(&subspace.positive);
        self.negative.remove_set(&subspace.negative);
    }

    /// Change the sign of all fixed variable.
    pub fn negate_all_variables(&mut self) {
        std::mem::swap(&mut self.positive, &mut self.negative);
    }

    /// Check if this pattern has some inner conflict
    pub fn has_conflict(&self) -> bool {
        !self.positive.is_disjoint(&self.negative)
    }

    /// Check if the pattern fixes some variables from the given set
    pub fn has_fixed_variables(&self, vars: &VarSet) -> bool {
        !self.positive.is_disjoint(vars) || !self.negative.is_disjoint(vars)
    }

    /// Restrict this pattern to its intersection with the given subspace.
    ///
    /// Returns false if the pattern has some conflict with the subspace (it remains unchanged)
    /// Returns true and eliminates unnecessary variables otherwise
    pub fn restrict(&mut self, subspace: &Pattern) -> bool {
        if !self.overlaps(subspace) {
            return false;
        }
        self.remove_shared_restrictions(subspace);
        true
    }

    /// Fix a variable to a specific value, even if it is already fixed at another.
    ///
    /// If this variable was free, this leads to a restriction of the pattern.
    /// If it was fixed to the same value, the pattern is unchanged.
    /// If it was fixed to the opposite value, a conflict is introduced
    pub fn set_ignoring_conflicts(&mut self, var: Variable, value: bool) {
        if value {
            self.positive.insert(var);
        } else {
            self.negative.insert(var);
        }
    }

    /// Extract the pattern emerging from a pair of patterns if it exists.
    ///
    /// A new pattern can emerge from a pair of patterns with a single conflict.
    /// The conflicting variable is removed and all other restrictions of the two original
    /// patterns are combined. Each of the initial pattern covers half of the new pattern.
    pub fn emerging_pattern(&self, other: &Self) -> Option<Self> {
        let mut pos = self.positive.clone();
        pos.insert_set(&other.positive);
        let mut neg = self.negative.clone();
        neg.insert_set(&other.negative);

        let mut conflicts = pos.clone();
        conflicts.retain_set(&neg);
        if conflicts.len() == 1 {
            pos.remove_set(&conflicts);
            neg.remove_set(&conflicts);
            return Some(Pattern::with(pos, neg));
        }
        None
    }

    /// Check if a state is contained in this patter
    pub fn contains_state(&self, state: &State) -> bool {
        state.as_ref().contains_set(&self.positive) && state.as_ref().is_disjoint(&self.negative)
    }

    /// Check if this pattern shares at least one state with another pattern
    ///
    /// returns false if at least variable is fixed at opposite values in both patterns.
    /// Conflicts are ignored as long as a conflicting variable in one of the patterns is free in the other one.
    pub fn overlaps(&self, other: &Pattern) -> bool {
        self.positive.is_disjoint(&other.negative) && self.negative.is_disjoint(&other.positive)
    }

    /// Test if this pattern contains the given pattern.
    pub fn contains_subspace(&self, p: &Pattern) -> bool {
        p.positive.contains_set(&self.positive) && p.negative.contains_set(&self.negative)
    }

    /// Test if all variables used in this pattern are contained in a given set
    pub fn variables_contained_in(&self, vars: &VarSet) -> bool {
        vars.contains_set(&self.positive) && vars.contains_set(&self.negative)
    }

    pub fn additional_len(&self) -> usize {
        self.positive.len() + self.negative.len()
    }

    #[cfg(feature = "pyo3")]
    fn __str__(&self) -> String {
        format!("{}", self)
    }

    #[cfg(feature = "pyo3")]
    fn __repr__(&self) -> String {
        format!("{:?}", self)
    }
}

impl FromStr for Pattern {
    type Err = BokitError;

    fn from_str(descr: &str) -> Result<Pattern, BokitError> {
        let mut p = Pattern::default();
        let mut idx = 0;
        for c in descr.chars() {
            match c {
                ' ' | '\t' | '\'' => (), // skip spacing and ` for formatting
                '-' => idx += 1,
                '0' => {
                    p.negative.insert(Variable(idx));
                    idx += 1;
                }
                '1' => {
                    p.positive.insert(Variable(idx));
                    idx += 1;
                }
                _ => return Err(BokitError::InvalidExpression),
            };
        }
        Ok(p)
    }
}

impl Not for Pattern {
    type Output = Expr;
    fn not(self) -> Self::Output {
        Expr::from(self).not()
    }
}

impl Rule for Pattern {
    fn fmt_with(&self, f: &mut dyn ExprFormatter) -> fmt::Result {
        f.write_pattern(self, true, None)
    }

    fn eval(&self, state: &State) -> bool {
        self.contains_state(state)
    }

    fn collect_regulators(&self, regulators: &mut VarSet) {
        regulators.insert_set(&self.positive);
        regulators.insert_set(&self.negative);
    }

    fn count_regulators(&self, regulators: &mut VariableCounter, value: bool) {
        regulators.push_pattern(self, value);
    }

    fn as_expression(&self) -> Cow<Expr> {
        Cow::Owned(Expr::from(self))
    }

    fn as_implicants(&self) -> Cow<Implicants> {
        Cow::Owned(Implicants::from(Expr::from(self)))
    }

    fn as_primes(&self) -> Cow<Primes> {
        Cow::Owned(Primes::from(Expr::from(self)))
    }
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut result = vec![];
        for v in &self.positive {
            if result.len() <= v.uid() {
                result.resize(v.uid() + 1, '-');
            }
            result[v.uid()] = '1';
        }
        for v in &self.negative {
            if self.positive.contains(v) {
                result[v.uid()] = '%';
            } else {
                if result.len() <= v.uid() {
                    result.resize(v.uid() + 1, '-');
                }
                result[v.uid()] = '0';
            }
        }
        let s: String = result.iter().collect();
        write!(f, "{}", &s)
    }
}

impl From<&Pattern> for Expr {
    fn from(pattern: &Pattern) -> Expr {
        let e = pattern.positive.iter().fold(Expr::from(true), |e, v| e & v);
        pattern.negative.iter().fold(e, |e, v| e & !v)
    }
}

impl From<Variable> for Pattern {
    fn from(var: Variable) -> Self {
        let mut pattern = Pattern::default();
        pattern.set(var, true);
        pattern
    }
}

#[cfg(test)]
mod tests {
    use crate::pattern::*;

    #[test]
    fn construct_and_display() -> Result<(), BokitError> {
        let p = Pattern::from_str("-0--01-11--0-1---")?;

        println!("{}", p);

        let mut p = Pattern::default();
        let pos = vec![1, 3, 5, 8];
        for v in pos {
            p.set(Variable(v), true);
        }

        // TODO: check that printing and parsing reproduces the same pattern

        Ok(())
    }

    #[test]
    fn emerging() -> Result<(), BokitError> {
        let p = Pattern::from_str("101--01---")?;
        let t = Pattern::from_str("-001")?;
        let t2 = Pattern::from_str("0001")?;

        assert_eq!(format!("{}", p), "101--01");

        let e = p.emerging_pattern(&t).unwrap();
        assert_eq!(format!("{}", e), "10-1-01");

        assert_eq!(p.emerging_pattern(&t2).is_none(), true);

        Ok(())
    }

    #[test]
    fn contained() {
        let mut p = Pattern::default();
        let mut t = Pattern::default();
        p.set(Variable(3), true);
        p.set(Variable(2), true);
        assert!(t.contains_subspace(&p));

        t.set(Variable(2), true);
        assert!(t.contains_subspace(&p));

        t.set(Variable(3), true);
        assert!(t.contains_subspace(&p));

        t.set(Variable(5), true);
        assert!(!t.contains_subspace(&p));
    }
}
