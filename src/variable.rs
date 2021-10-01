//! Implementation for variables and their naming in rules

use crate::*;

use crate::space::VarSpace;
use bit_set::BitSet;
use once_cell::sync::Lazy;
use regex::Regex;
use std::fmt;
use std::iter::FromIterator;
use std::str::FromStr;

#[cfg(feature = "pyo3")]
use pyo3::{prelude::*, PyObjectProtocol};

static RE_GENERIC_NAME: Lazy<Regex> = Lazy::new(|| Regex::new(r"^\s*_?([01-9]+)_?\s*$").unwrap());

/// A single Boolean variable with an integer UID.
///
/// A variable or its raw UID can be used to set or retrieve the value of the variable in a [State] or [Pattern],
/// but also to define atoms in [expression trees](Expr).
///
/// They can be created manually by specifying the UID, or through a [variable collection](VarSpace)
/// where they are associated to a human-readable identifier.
#[cfg_attr(feature = "pyo3", pyclass(module = "bokit"))]
#[derive(Clone, Copy, Default, Debug, Eq, Hash, PartialEq)]
pub struct Variable(pub(crate) usize);

impl Variable {
    /// Create a new variable with a specific UID
    pub fn new(uid: usize) -> Self {
        Self(uid)
    }
}

#[cfg_attr(feature = "pyo3", pymethods)]
impl Variable {
    /// Create a new variable with a specific UID
    #[cfg(feature = "pyo3")]
    #[new]
    pub fn py_new(uid: usize) -> Self {
        Self(uid)
    }

    /// Return the internal integer UID
    pub fn uid(&self) -> usize {
        self.0
    }

    #[cfg(feature = "pyo3")]
    #[pyo3(name = "eval")]
    pub fn py_eval(&self, state: &State) -> bool {
        self.eval(state)
    }
}

impl From<usize> for Variable {
    fn from(uid: usize) -> Self {
        Self(uid)
    }
}

impl Rule for Variable {
    fn fmt_rule(&self, f: &mut fmt::Formatter, namer: &VarSpace) -> fmt::Result {
        namer.format_variable(f, *self)
    }

    fn eval(&self, state: &State) -> bool {
        state.is_active(*self)
    }

    fn collect_regulators(&self, regulators: &mut VarSet) {
        regulators.insert(*self);
    }
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_{}_", self.0)
    }
}

#[cfg(feature = "pyo3")]
#[pyproto]
impl PyObjectProtocol<'_> for Variable {
    fn __str__(&self) -> String {
        format!("{}", self)
    }
    fn __repr__(&self) -> String {
        format!("{:?}", self)
    }
}

impl FromStr for Variable {
    type Err = BokitError;

    fn from_str(name: &str) -> Result<Self, Self::Err> {
        if let Some(cap) = RE_GENERIC_NAME.captures(name) {
            let uid: usize = cap.get(1).unwrap().as_str().parse().unwrap();
            return Ok(Variable::from(uid));
        }
        Err(BokitError::InvalidExpression)
    }
}

/// A set of selected variables with efficient bitwise operations.
///
/// A VarSet is an abstraction over [BitSet], providing a similar API.
/// It can be constructed explicitly by inserting or removing individual variables, or by importing
/// an existing collection of variables. Union, intersection and differences are bitwise operations.
///
/// A VarSet can also be parsed from strings where the position in the string defines the
/// variable UID and the character defines the activation state: 0 for inactive, 1 for active.
/// To make the strings easier to read, spaces and ' are ignored around and inside the string.
/// For example "001001100", "  001001100", and "00100 1100" are equivalent.
///
/// ```
/// use bokit::{Variable, VarSet};
///
/// let mut vs = VarSet::default();
/// let mut var = Variable::from(3);
/// vs.insert(1);
/// vs.insert(var);
/// vs.remove(3);
///
/// # assert!(!vs.contains(0));
/// # assert!( vs.contains(1));
/// # assert!(!vs.contains(3));
/// ```
#[cfg_attr(feature = "pyo3", pyclass(module = "bokit"))]
#[derive(Clone, PartialEq, Eq, Default, Debug)]
pub struct VarSet {
    pub variables: BitSet,
}

// These functions can not be directly mapped to Python methods
impl VarSet {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create an iterator over the contained variables
    pub fn iter(&self) -> Iter {
        self.into_iter()
    }
}

#[cfg_attr(feature = "pyo3", pymethods)]
impl VarSet {
    #[cfg(feature = "pyo3")]
    #[new]
    /// Create an empty set of variables
    pub fn py_new() -> Self {
        Self::new()
    }

    /// Activate the given variable in this state
    pub fn insert(&mut self, var: Variable) {
        self.variables.insert(var.uid());
    }

    /// Disable the given variable in this state
    pub fn remove(&mut self, var: Variable) {
        self.variables.remove(var.uid());
    }

    /// Test if a specific variable is active in this state
    pub fn contains(&self, var: Variable) -> bool {
        self.variables.contains(var.uid())
    }

    /// Remove all variables from the other set
    pub fn difference_with(&mut self, vars: &Self) {
        self.variables.difference_with(&vars.variables);
    }

    /// Retain only the variables also included in the other set
    pub fn intersect_with(&mut self, vars: &Self) {
        self.variables.intersect_with(&vars.variables);
    }

    /// Add all variables from the other set
    pub fn union_with(&mut self, vars: &Self) {
        self.variables.union_with(&vars.variables);
    }

    /// Return true if this set contains all variables of the other set
    pub fn contains_all(&self, other: &Self) -> bool {
        self.variables.is_superset(&other.variables)
    }

    /// Return true if the two sets have no common variable
    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.variables.is_disjoint(&other.variables)
    }

    /// Return the number of variables in this set
    pub fn len(&self) -> usize {
        self.variables.len()
    }

    /// Return whether there are no selected variable in this set
    pub fn is_empty(&self) -> bool {
        self.variables.is_empty()
    }
}

impl From<BitSet> for VarSet {
    fn from(variables: BitSet) -> Self {
        Self { variables }
    }
}

impl From<&BitSet> for VarSet {
    fn from(variables: &BitSet) -> Self {
        Self {
            variables: variables.clone(),
        }
    }
}

impl From<VarSet> for BitSet {
    fn from(vs: VarSet) -> Self {
        vs.variables
    }
}

impl AsRef<BitSet> for VarSet {
    fn as_ref(&self) -> &BitSet {
        &self.variables
    }
}

impl AsMut<BitSet> for VarSet {
    fn as_mut(&mut self) -> &mut BitSet {
        &mut self.variables
    }
}

impl FromIterator<Variable> for VarSet {
    fn from_iter<I: IntoIterator<Item = Variable>>(iter: I) -> Self {
        let mut vs = VarSet::default();
        for v in iter {
            vs.insert(v);
        }
        vs
    }
}

impl Extend<Variable> for VarSet {
    fn extend<T: IntoIterator<Item = Variable>>(&mut self, iter: T) {
        for v in iter {
            self.insert(v);
        }
    }
}

impl fmt::Display for VarSet {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut pos = 0;
        for v in self {
            while pos < v.uid() {
                write!(f, "0")?;
                pos += 1;
            }
            write!(f, "1")?;
            pos += 1;
        }
        write!(f, "")
    }
}

#[cfg(feature = "pyo3")]
#[pyproto]
impl PyObjectProtocol<'_> for VarSet {
    fn __str__(&self) -> String {
        format!("{}", self)
    }
    fn __repr__(&self) -> String {
        format!("{:?}", self)
    }
}

impl FromStr for VarSet {
    type Err = BokitError;

    fn from_str(descr: &str) -> Result<Self, BokitError> {
        let mut s = Self::default();
        let mut idx = 0;
        for c in descr.chars() {
            match c {
                ' ' | '\t' | '\'' => (), // skip spacing and ` for formatting
                '0' => idx += 1,
                '1' => {
                    s.insert(Variable(idx));
                    idx += 1;
                }
                _ => return Err(BokitError::InvalidExpression),
            };
        }
        Ok(s)
    }
}

/// Iterate over variables in a [VarSet]
pub struct Iter<'a>(bit_set::Iter<'a, u32>);

impl Iterator for Iter<'_> {
    type Item = Variable;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|uid| uid.into())
    }
}

impl<'a> IntoIterator for &'a VarSet {
    type Item = Variable;
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        Iter(self.variables.iter())
    }
}

#[cfg(test)]
mod tests {
    use crate::*;
    use core::str::FromStr;

    #[test]
    fn extract_variable() -> Result<(), BokitError> {
        // the empty namer should recognize only generic names
        assert_eq!(Variable::from_str("12").unwrap().uid, 12);
        assert_eq!(Variable::from_str("_003_").unwrap().uid, 3);
        assert_eq!(Variable::from_str("  5_  ").unwrap().uid, 5);

        assert_eq!(Variable::from_str("h12").is_err(), true);
        assert_eq!(Variable::from_str("v1y2").is_err(), true);

        let mut varset = VarSpace::default();
        let vtest = varset.add("test")?;
        let valt = varset.add("alternative")?;

        assert_eq!(true, varset.add("3test").is_err());
        assert_eq!(true, varset.add("te%t").is_err());
        assert_eq!(vtest, varset.add("test")?);

        assert_eq!(vtest, varset.get_variable("test")?);
        assert_eq!(valt, varset.get_variable("alternative")?);

        assert_eq!(true, varset.get_variable("pipo").is_err());

        Ok(())
    }

    #[test]
    fn extract_state() -> Result<(), BokitError> {
        let mut variables = VarSpace::default();
        let v1 = variables.add("A")?;
        let v2 = variables.add("B")?;
        let v3 = variables.add("C")?;
        let v4 = variables.add("D")?;
        let v5 = variables.add("E")?;

        let state = variables.get_state("A D E; B, D")?;
        assert_eq!(state.active.len(), 4);
        assert_eq!(state.is_active(v1), true);
        assert_eq!(state.is_active(v2), true);
        assert_eq!(state.is_active(v3), false);
        assert_eq!(state.is_active(v4), true);
        assert_eq!(state.is_active(v5), true);

        let mut varset = VarSpace::default();
        varset.add("test")?;
        varset.add("alternative")?;
        varset.add("third")?;

        let state = varset.get_state("test third")?;
        assert_eq!(2, state.active.len());
        assert_eq!(true, state.active.contains(0));
        assert_eq!(true, state.active.contains(2));

        Ok(())
    }

    #[test]
    fn uid_provider() {
        let mut uids = VarSpace::default();
        assert_eq!(uids.add("a").unwrap().uid, 0);
        assert_eq!(uids.add("b").unwrap().uid, 1);
        assert_eq!(uids.add("c").unwrap().uid, 2);
        assert_eq!(uids.add("d").unwrap().uid, 3);

        assert_eq!(uids.len(), (&uids).into_iter().count());
        assert_eq!(uids.len(), 4);

        uids.remove_variable(2);
        uids.remove_variable(0);
        assert_eq!(uids.len(), (&uids).into_iter().count());
        assert_eq!(uids.len(), 2);

        uids.remove_variable(2);
        assert_eq!(uids.len(), (&uids).into_iter().count());
        assert_eq!(uids.len(), 2);

        uids.add("e").unwrap().uid;
        uids.remove_variable(3);
        assert_eq!(uids.len(), (&uids).into_iter().count());
        assert_eq!(uids.len(), 2);

        assert_eq!(uids.len(), (&uids).into_iter().count());
    }

    #[test]
    fn components() {
        let mut uids = VarSpace::default();

        let v0 = uids.add("a").unwrap();
        let v1 = uids.add("b").unwrap();
        let v1_0 = uids.associate(1, 0).unwrap();
        let v1_2 = uids.associate(1, 2).unwrap();
        let v1_1 = uids.associate(1, 1).unwrap();
        let v4 = uids.add("c").unwrap();
        let v5 = uids.add("d").unwrap();

        assert_eq!(v0.uid, 0);
        assert_eq!(v1.uid, 1);
        assert_eq!(v1_0.uid, 1);
        assert_eq!(v1_2.uid, 3);
        assert_eq!(v4.uid, 4);
        assert_eq!(v5.uid, 5);

        assert_eq!(uids.into_iter().count(), 6);
        assert_eq!(uids.iter_components().count(), 4);

        assert_eq!(format!("{}", uids.named(&v1)), "b:0");
        assert_eq!(format!("{}", uids.named(&v1_2)), "b:2");

        uids.remove_variable(v1_1);
        assert_eq!(uids.into_iter().count(), 5);
        assert_eq!(uids.iter_components().count(), 4);
        assert_eq!(format!("{}", uids.named(&v1)), "b:0");
        assert_eq!(format!("{}", uids.named(&v1_2)), "b:1");

        uids.remove_variable(v1);
        assert_eq!(uids.into_iter().count(), 4);
        assert_eq!(uids.iter_components().count(), 4);

        assert_eq!(format!("{}", uids.named(&v1_2)), "b");
    }

    #[test]
    fn check_rule() {
        let mut uids = VarSpace::default();

        let v0 = uids.add("a").unwrap();
        let v1 = uids.add("b").unwrap();

        let expr = v0 | v1;
        assert_eq!(uids.check_rule(&expr).is_ok(), true);

        let v5 = Variable::from(5);
        let expr = v0 | v1 | (v5 & !v5);
        assert_eq!(uids.check_rule(&expr).is_ok(), false);

        let primes = Primes::from(&expr);
        assert_eq!(uids.check_rule(&primes).is_ok(), true);
    }
}
