use crate::variable::Iter;
use crate::{BokitError, VarSet, Variable};
use std::fmt;
use std::iter::FromIterator;
use std::str::FromStr;

#[cfg(feature = "pyo3")]
use pyo3::prelude::*;

/// A state defined by the set of active variables, the others are implicitly inactive.
///
/// Here states are defined as sets of all active variables (using bit-sets internally) and all other variables
/// are implicitly considered as inactive.
///
/// Just like the underlying [VarSet], a state can be constructed explicitly by activating or disabling
/// individual variables, or by importing an existing collection of variables, or parsed from a string.
///
/// ```
/// use bokit::{State, Variable};
/// use std::iter::FromIterator;
///
/// let mut var = Variable::from(3);
///
/// let mut state = State::default();
/// state.activate(1);
/// state.activate(var);
/// state.disable(2);
/// state.disable(3);
///
/// // Build a state from a list of UIDs (variables or usize)
/// let state2 = State::from_iter([2,4,6]);
///
/// assert_eq!(state.is_active(0), false);
/// assert_eq!(state.is_active(1), true);
/// assert_eq!(state.is_active(2), false);
/// assert_eq!(state.is_active(3), false);
///
/// // Parse state strings
/// let state3: State = "0010 01100".parse().unwrap();
/// ```
#[cfg_attr(feature = "pyo3", pyclass(module = "bokit"))]
#[derive(Clone, Default, Debug)]
pub struct State {
    pub(crate) active: VarSet,
}

impl State {
    /// Activate the given variable in this state
    pub fn activate(&mut self, var: Variable) {
        self.active.insert(var);
    }

    /// Disable the given variable in this state
    pub fn disable(&mut self, var: Variable) {
        self.active.remove(var);
    }

    /// Test if a specific variable is active in this state
    pub fn is_active(&self, var: Variable) -> bool {
        self.active.contains(var)
    }

    pub fn active(&self) -> &VarSet {
        &self.active
    }

    pub fn active_mut(&mut self) -> &mut VarSet {
        &mut self.active
    }

    /// Iterate over the set of active variables
    pub fn iter_active(&self) -> Iter {
        self.active.iter()
    }

    /// Return the set of active variables
    pub fn into(self) -> VarSet {
        self.active
    }
}

impl<T: Into<VarSet>> From<T> for State {
    fn from(vs: T) -> Self {
        Self { active: vs.into() }
    }
}

impl FromIterator<Variable> for State {
    fn from_iter<I: IntoIterator<Item = Variable>>(iter: I) -> Self {
        Self::from(VarSet::from_iter(iter))
    }
}

impl Extend<Variable> for State {
    fn extend<T: IntoIterator<Item = Variable>>(&mut self, iter: T) {
        self.active.extend(iter);
    }
}

impl<'a> IntoIterator for &'a State {
    type Item = Variable;
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.active.iter()
    }
}

impl FromStr for State {
    type Err = BokitError;

    fn from_str(descr: &str) -> Result<State, BokitError> {
        let vs: VarSet = descr.parse()?;
        Ok(Self::from(vs))
    }
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self.active)
    }
}
