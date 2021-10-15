use crate::*;

use std::fmt;
use std::fmt::Formatter;
use std::iter::FromIterator;
use std::str::FromStr;

#[cfg(feature = "pyo3")]
use pyo3::{prelude::*, PyObjectProtocol};

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
    /// Create a pattern from the two inner sets of fixed variables
    pub fn with(positive: VarSet, negative: VarSet) -> Self {
        Self { positive, negative }
    }

    /// Create a pattern restricted to a single state
    /// To properly set all variables fixed at 0, this requires
    /// an extra parameter giving the list of variables.
    pub fn from_state(state: State, variables: impl IntoIterator<Item = Variable>) -> Pattern {
        let mut neg = VarSet::from_iter(variables);
        let mut pos = state.into();
        pos.intersect_with(&neg);
        neg.difference_with(&pos);
        Pattern::with(pos, neg)
    }

    /// Parse a pattern using the specified variables
    ///
    /// Instead of using naturally ordered variables as in the default parser, we use
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

    /// Clone and restrict if no conflict is introduced.
    pub fn try_set(&self, var: Variable, value: bool) -> Option<Self> {
        if self.has_restriction(var, !value) {
            return None;
        }
        let mut result = self.clone();
        result.set_ignoring_conflicts(var, value);
        Some(result)
    }

    /// Test if a variable is fixed at a specific value in this pattern
    pub fn has_restriction(&self, var: Variable, value: bool) -> bool {
        if value {
            self.positive.contains(var)
        } else {
            self.negative.contains(var)
        }
    }

    /// Extract the pattern emerging from a pair of patterns if it exists.
    ///
    /// A new pattern can emerge from a pair of patterns with a single conflict.
    /// The conflicting variable is removed and all other restrictions of the two original
    /// patterns are combined. Each of the initial pattern covers half of the new pattern.
    pub fn emerging_pattern(&self, other: &Self) -> Option<Self> {
        let mut pos = self.positive.clone();
        pos.union_with(&other.positive);
        let mut neg = self.negative.clone();
        neg.union_with(&other.negative);

        let mut conflicts = pos.variables.intersection(&neg.variables);
        if let Some(uid) = conflicts.next() {
            if conflicts.next().is_none() {
                pos.remove(Variable::new(uid));
                neg.remove(Variable::new(uid));
                return Some(Pattern::with(pos, neg));
            }
        }
        None
    }

    /// Check if a state is contained in this patter
    pub fn contains_state(&self, state: &State) -> bool {
        state.active.contains_all(&self.positive) && state.active.is_disjoint(&self.negative)
    }

    /// Check if this pattern shares at least one state with another pattern
    pub fn overlaps(&self, other: &Pattern) -> bool {
        self.positive.is_disjoint(&other.negative) && self.negative.is_disjoint(&other.positive)
    }

    /// Test if this pattern contains the given pattern.
    pub fn contains(&self, p: &Pattern) -> bool {
        p.positive.contains_all(&self.positive) && p.negative.contains_all(&self.negative)
    }

    /// Test if all variables used in this pattern are contained in a given set
    pub fn variables_contained_in(&self, vars: &VarSet) -> bool {
        vars.contains_all(&self.positive) && vars.contains_all(&self.negative)
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

impl Rule for Pattern {
    fn fmt_rule(&self, f: &mut Formatter, _collection: &VarSpace) -> fmt::Result {
        write!(f, "{}", self)
    }

    fn eval(&self, state: &State) -> bool {
        self.contains_state(state)
    }

    fn collect_regulators(&self, regulators: &mut VarSet) {
        regulators.union_with(&self.positive);
        regulators.union_with(&self.negative);
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

#[cfg(feature = "pyo3")]
#[pyproto]
impl PyObjectProtocol<'_> for Pattern {
    fn __str__(&self) -> String {
        format!("{}", self)
    }
    fn __repr__(&self) -> String {
        format!("{:?}", self)
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
        assert!(t.contains(&p));

        t.set(Variable(2), true);
        assert!(t.contains(&p));

        t.set(Variable(3), true);
        assert!(t.contains(&p));

        t.set(Variable(5), true);
        assert!(!t.contains(&p));
    }
}
