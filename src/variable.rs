//! Implementation for variables and their naming in rules

use crate::parse::VariableParser;
use crate::*;
use std::borrow::Cow;

use bit_set::BitSet;
use std::fmt;
use std::iter::FromIterator;
use std::str::FromStr;

use crate::efmt::ExprFormatter;
use crate::error::ParseError;
#[cfg(feature = "pyo3")]
use crate::pyborrowed::{borrow_iterator, BoxedPyIterator};
#[cfg(feature = "pyo3")]
use pyo3::prelude::*;
use std::ops::Not;

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

#[derive(Clone, Default, Debug)]
pub struct VariableCounter {
    counts: HashMap<Variable, (usize, usize)>,
}

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
    pub fn new_py(uid: usize) -> Self {
        Self::new(uid)
    }

    /// Return the internal integer UID
    pub fn uid(&self) -> usize {
        self.0
    }

    /// Evaluate the rule on the given state
    #[cfg(feature = "pyo3")]
    #[pyo3(name = "eval")]
    pub fn eval_py(&self, state: &State) -> bool {
        self.eval(state)
    }

    #[cfg(feature = "pyo3")]
    fn __str__(&self) -> String {
        format!("{}", self)
    }

    #[cfg(feature = "pyo3")]
    fn __repr__(&self) -> String {
        format!("{:?}", self)
    }

    #[cfg(feature = "pyo3")]
    fn __or__(&self, rhs: &PyAny) -> PyResult<Expr> {
        Expr::from(*self).__or__(rhs)
    }

    #[cfg(feature = "pyo3")]
    fn __and__(&self, rhs: &PyAny) -> PyResult<Expr> {
        Expr::from(*self).__and__(rhs)
    }

    #[cfg(feature = "pyo3")]
    fn __invert__(&self) -> Expr {
        !Expr::from(*self)
    }
}

impl From<usize> for Variable {
    fn from(uid: usize) -> Self {
        Self(uid)
    }
}

impl Rule for Variable {
    fn fmt_with(&self, f: &mut dyn ExprFormatter) -> fmt::Result {
        f.write_variable(*self, true)
    }

    fn eval(&self, state: &State) -> bool {
        state.is_active(*self)
    }

    fn collect_regulators(&self, regulators: &mut VarSet) {
        regulators.insert(*self);
    }

    fn count_regulators(&self, regulators: &mut VariableCounter, value: bool) {
        regulators.push(*self, value);
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

impl VariableCounter {
    pub fn push_pattern(&mut self, p: &Pattern, value: bool) {
        for (var, val) in p.iter_fixed_values() {
            self.push(var, val == value);
        }
    }

    pub fn push(&mut self, var: Variable, value: bool) {
        let mut v = self.counts.entry(var).or_insert_with(|| (0, 0));
        if value {
            v.1 += 1;
        } else {
            v.0 += 1;
        }
    }
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_{}_", self.uid())
    }
}

impl FromStr for Variable {
    type Err = BokitError;

    fn from_str(name: &str) -> Result<Self, Self::Err> {
        parse::parser().parse_variable(name)
    }
}

impl Not for Variable {
    type Output = Expr;
    fn not(self) -> Self::Output {
        Expr::from(self).not()
    }
}

/// A set of selected variables with efficient bitwise operations.
///
/// A `VarSet` is an abstraction over [`BitSet`], providing a similar API.
/// It can be constructed explicitly by inserting or removing individual variables, or by importing
/// an existing collection of variables. Union, intersection and differences are bitwise operations.
///
/// A `VarSet` can also be parsed from strings where the position in the string defines the
/// variable UID and the character defines the activation state: 0 for inactive, 1 for active.
/// To make the strings easier to read, spaces and ' are ignored around and inside the string.
/// For example "001001100", "  001001100", and "00100 1100" are equivalent.
///
/// ```
/// use bokit::{Variable, VarSet};
///
/// let mut vs = VarSet::default();
/// let v0 = Variable::from(0);
/// let v1 = Variable::from(1);
/// let v3 = Variable::from(3);
/// vs.insert(v1);
/// vs.insert(v3);
/// vs.remove(v3);
///
/// # assert!(!vs.contains(v0));
/// # assert!( vs.contains(v1));
/// # assert!(!vs.contains(v3));
/// ```
#[cfg_attr(feature = "pyo3", pyclass(module = "bokit"))]
#[derive(Clone, PartialEq, Eq, Default, Debug)]
pub struct VarSet(BitSet);

/// An ordered list of variables, without duplicates
#[cfg_attr(feature = "pyo3", pyclass(module = "bokit"))]
#[derive(Clone, PartialEq, Eq, Default, Debug)]
pub struct VarList {
    varset: VarSet,
    varlist: Vec<Variable>,
}

impl VarList {
    pub fn iter(&self) -> impl Iterator<Item = &Variable> {
        self.varlist.iter()
    }

    pub fn len(&self) -> usize {
        self.varlist.len()
    }
}

#[cfg_attr(feature = "pyo3", pymethods)]
impl VarList {
    pub fn push(&mut self, var: Variable) -> Result<(), BokitError> {
        if self.varset.contains(var) {
            // TODO: error duplicate variable
            return Err(BokitError::InvalidExpression);
        }

        self.varset.insert(var);
        self.varlist.push(var);
        Ok(())
    }

    pub fn is_empty(&self) -> bool {
        self.varlist.is_empty()
    }

    #[cfg(feature = "pyo3")]
    fn __str__(&self) -> String {
        format!("{}", self)
    }

    #[cfg(feature = "pyo3")]
    fn __repr__(&self) -> String {
        format!("{:?}", self)
    }

    #[cfg(feature = "pyo3")]
    fn __len__(&self) -> usize {
        self.len()
    }

    #[cfg(feature = "pyo3")]
    fn __iter__(slf: Py<Self>, py: Python) -> Option<BoxedPyIterator> {
        borrow_iterator(py, slf, |v| v.iter().copied())
    }
}

// These functions can not be directly mapped to Python methods
impl VarSet {
    /// Create an empty set of variables (same as default)
    pub fn new() -> Self {
        Self::default()
    }

    /// Create an iterator over the contained variables
    pub fn iter(&self) -> Iter {
        self.into_iter()
    }

    pub fn parse(text: &str) -> Result<Self, BokitError> {
        parse::parser().parse_variable_set(text)
    }
}

#[cfg_attr(feature = "pyo3", pymethods)]
impl VarSet {
    #[cfg(feature = "pyo3")]
    #[new]
    /// Create an empty set of variables
    pub fn new_py() -> Self {
        Self::new()
    }

    /// Get the number of variables in this set
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Check if this set is empty (i.e. contains no variable)
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Test if a specific variable is included in this set
    pub fn contains(&self, var: Variable) -> bool {
        self.0.contains(var.uid())
    }

    /// Return true if this set contains all variables of the other set
    pub fn contains_set(&self, other: &Self) -> bool {
        self.0.is_superset(&other.0)
    }

    /// Return true if the two sets have no common variable
    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.0.is_disjoint(&other.0)
    }

    /// Include the given variable in this set
    pub fn insert(&mut self, var: Variable) {
        self.0.insert(var.uid());
    }

    /// Add all variables from the other set
    pub fn insert_set(&mut self, vars: &Self) {
        self.0.union_with(&vars.0);
    }

    /// Remove the given variable from this state
    pub fn remove(&mut self, var: Variable) {
        self.0.remove(var.uid());
    }

    /// Remove all variables from the other set
    pub fn remove_set(&mut self, vars: &Self) {
        self.0.difference_with(&vars.0);
    }

    /// Remove all variables from this set
    pub fn clear(&mut self) {
        self.0.clear()
    }

    /// Retain only the variables included in the other set
    pub fn retain_set(&mut self, vars: &Self) {
        self.0.intersect_with(&vars.0);
    }

    #[cfg(feature = "pyo3")]
    fn __str__(&self) -> String {
        format!("{}", self)
    }

    #[cfg(feature = "pyo3")]
    fn __repr__(&self) -> String {
        format!("{:?}", self)
    }

    #[cfg(feature = "pyo3")]
    fn __len__(&self) -> usize {
        self.len()
    }

    #[cfg(feature = "pyo3")]
    fn __iter__(slf: Py<Self>, py: Python) -> Option<BoxedPyIterator> {
        borrow_iterator(py, slf, |v| v.iter())
    }
}

impl From<BitSet> for VarSet {
    fn from(variables: BitSet) -> Self {
        Self(variables)
    }
}

impl From<VarSet> for BitSet {
    fn from(vs: VarSet) -> Self {
        vs.0
    }
}

impl AsRef<BitSet> for VarSet {
    fn as_ref(&self) -> &BitSet {
        &self.0
    }
}

impl AsMut<BitSet> for VarSet {
    fn as_mut(&mut self) -> &mut BitSet {
        &mut self.0
    }
}

impl FromIterator<Variable> for VarSet {
    fn from_iter<I: IntoIterator<Item = Variable>>(iter: I) -> Self {
        let mut vs = Self::default();
        vs.extend(iter);
        vs
    }
}

impl Extend<Variable> for VarSet {
    fn extend<T: IntoIterator<Item = Variable>>(&mut self, iter: T) {
        iter.into_iter().for_each(|v| self.insert(v));
    }
}

impl fmt::Display for VarSet {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut first = true;
        write!(f, "{{")?;
        for v in self {
            match first {
                true => first = false,
                false => write!(f, ", ")?,
            }
            write!(f, "{}", v.uid())?;
        }
        write!(f, "}}")
    }
}

impl fmt::Display for VarList {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut first = true;
        write!(f, "(")?;
        for v in &self.varlist {
            match first {
                true => first = false,
                false => write!(f, ", ")?,
            }
            write!(f, "{}", v.uid())?;
        }
        write!(f, ")")
    }
}

impl FromStr for VarSet {
    type Err = ParseError;

    fn from_str(descr: &str) -> Result<Self, Self::Err> {
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
                _ => return Err(ParseError::ParsingFailed(descr.to_string(), "VarSet")),
            };
        }
        Ok(s)
    }
}

/// Iterate over variables in a [`VarSet`]
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
        Iter(self.0.iter())
    }
}

#[cfg(test)]
mod tests {
    use crate::variable::VariableCounter;
    use crate::{parse::VariableParser, *};
    use core::str::FromStr;

    #[test]
    fn extract_variable() -> Result<(), BokitError> {
        // the empty namer should recognize only generic names
        assert_eq!(Variable::from_str("12").unwrap().uid(), 12);
        assert_eq!(Variable::from_str("_003_").unwrap().uid(), 3);
        assert_eq!(Variable::from_str("  5_  ").unwrap().uid(), 5);

        assert_eq!(Variable::from_str("h12").is_err(), true);
        assert_eq!(Variable::from_str("v1y2").is_err(), true);

        let mut varset = VarSpace::default();
        let vtest = varset.provide("test")?;
        let valt = varset.provide("alternative")?;

        assert_eq!(true, varset.provide("3test").is_err());
        assert_eq!(true, varset.provide("te%t").is_err());
        assert_eq!(vtest, varset.provide("test")?);

        assert_eq!(vtest, varset.get_or_err("test")?);
        assert_eq!(valt, varset.get_or_err("alternative")?);

        assert_eq!(true, varset.get("pipo").is_none());

        Ok(())
    }

    #[test]
    fn extract_state() -> Result<(), BokitError> {
        let mut variables = VarSpace::default();
        let v1 = variables.provide("A")?;
        let v2 = variables.provide("B")?;
        let v3 = variables.provide("C")?;
        let v4 = variables.provide("D")?;
        let v5 = variables.provide("E")?;

        let state = variables.parse_state("A D E; B, D")?;
        assert_eq!(state.len_active(), 4);
        assert_eq!(state.is_active(v1), true);
        assert_eq!(state.is_active(v2), true);
        assert_eq!(state.is_active(v3), false);
        assert_eq!(state.is_active(v4), true);
        assert_eq!(state.is_active(v5), true);

        let mut varset = VarSpace::default();
        varset.provide("test")?;
        varset.provide("alternative")?;
        varset.provide("third")?;

        let state = varset.parse_state("test third")?;
        assert_eq!(2, state.len_active());
        assert_eq!(true, state.is_active(Variable(0)));
        assert_eq!(true, state.is_active(Variable(2)));

        Ok(())
    }

    #[test]
    fn uid_provider() -> Result<(), BokitError> {
        let mut uids = VarSpace::default();

        let va = uids.provide("a")?;
        let vb = uids.provide("b")?;
        let vc = uids.provide("c")?;
        let vd = uids.provide("d")?;

        assert_eq!(va.uid(), 0);
        assert_eq!(vb.uid(), 1);
        assert_eq!(vc.uid(), 2);
        assert_eq!(vd.uid(), 3);

        assert_eq!(uids.provide("b")?, vb);
        assert_eq!(uids.provide("d")?, vd);

        assert_eq!(uids.len(), (&uids).into_iter().count());
        assert_eq!(uids.len(), 4);

        uids.remove(vc);
        uids.remove(va);
        assert_eq!(uids.len(), (&uids).into_iter().count());
        assert_eq!(uids.len(), 2);

        uids.remove(vc);
        assert_eq!(uids.len(), (&uids).into_iter().count());
        assert_eq!(uids.len(), 2);

        uids.provide("e")?;
        uids.remove(vd);
        assert_eq!(uids.len(), (&uids).into_iter().count());
        assert_eq!(uids.len(), 2);

        assert_eq!(uids.len(), (&uids).into_iter().count());
        Ok(())
    }

    #[test]
    fn components() -> Result<(), BokitError> {
        let mut uids = VarSpace::default();

        let v0 = uids.provide("a")?;
        let v1 = uids.provide("b")?;
        let v1_0 = uids.provide("b:0")?;
        let v1_2 = uids.provide("b:2")?;
        let v1_1 = uids.provide("b:1")?;
        let v4 = uids.provide("c")?;
        let v5 = uids.provide("d")?;

        assert_eq!(v0.uid(), 0);
        assert_eq!(v1.uid(), 1);
        assert_eq!(v1_0.uid(), 1);
        assert_eq!(v1_2.uid(), 3);
        assert_eq!(v4.uid(), 4);
        assert_eq!(v5.uid(), 5);

        assert_eq!(uids.into_iter().count(), 6);
        assert_eq!(uids.iter_components().count(), 4);

        assert_eq!(format!("{}", uids.named(&v1)), "b:0");
        assert_eq!(format!("{}", uids.named(&v1_2)), "b:2");

        uids.remove(v1_1);
        assert_eq!(uids.into_iter().count(), 5);
        assert_eq!(uids.iter_components().count(), 4);
        assert_eq!(format!("{}", uids.named(&v1)), "b:0");
        assert_eq!(format!("{}", uids.named(&v1_2)), "b:1");

        uids.remove(v1);
        assert_eq!(uids.into_iter().count(), 4);
        assert_eq!(uids.iter_components().count(), 4);

        assert_eq!(format!("{}", uids.named(&v1_2)), "b");

        Ok(())
    }

    #[test]
    fn check_rule() {
        let mut uids = VarSpace::default();

        let v0 = uids.provide("a").unwrap();
        let v1 = uids.provide("b").unwrap();

        let expr = v0 | v1;
        assert_eq!(uids.check_rule(&expr).is_ok(), true);

        let v5 = Variable::from(5);

        let expr = v0 | v1 | v5;
        let primes = Primes::from(&expr);
        assert_eq!(uids.check_rule(&expr).is_ok(), false);
        assert_eq!(uids.check_rule(&primes).is_ok(), false);

        // Some unnecessary variables are eliminated from the expression
        let expr = v0 | v1 | (v5 & !v5);
        let primes = Primes::from(&expr);
        assert_eq!(uids.check_rule(&expr).is_ok(), true);
        assert_eq!(uids.check_rule(&primes).is_ok(), true);

        // Some unnecessary variables are only eliminated in the prime implicants
        let expr = v0 | (v1 & v5) | (v1 & !v5);
        let primes = Primes::from(&expr);
        assert_eq!(uids.check_rule(&expr).is_ok(), false);
        assert_eq!(uids.check_rule(&primes).is_ok(), true);
    }

    #[test]
    fn counter() {
        let mut counter = VariableCounter::default();

        counter.push(Variable(3), true);
        counter.push(Variable(5), true);
        counter.push(Variable(3), true);
        counter.push(Variable(7), false);
        counter.push(Variable(7), true);

        assert_eq!(None, counter.counts.get(&Variable(1)));
        assert_eq!(Some(&(0, 2)), counter.counts.get(&Variable(3)));
        assert_eq!(Some(&(1, 1)), counter.counts.get(&Variable(7)));
    }
}
