use crate::variable::Iter;
use crate::{BokitError, VarSet, Variable};
use std::fmt;
use std::iter::FromIterator;
use std::str::FromStr;

#[cfg(feature = "pyo3")]
use pyo3::prelude::*;

/// A state defined as a set of active variables, the others are implicitly inactive.
///
/// Here states are defined as [sets of active variables](VarSet) and all other variables
/// are implicitly considered as inactive.
/// Just like the underlying [VarSet], a state can be constructed explicitly by activating or disabling
/// individual variables, or by importing an existing collection of variables, or parsed from a string.
///
/// ```
/// use bokit::{State, Variable};
/// use std::iter::FromIterator;
///
/// let v0 = Variable::new(0);
/// let v1 = Variable::new(1);
/// let v2 = Variable::new(2);
/// let v3 = Variable::new(3);
/// let v4 = Variable::new(4);
/// let v6 = Variable::new(6);
///
/// let mut state = State::new();
/// state.activate(v1);
/// state.activate(v3);
/// state.disable(v2);
/// state.disable(v3);
///
/// // Build a state from a list of UIDs (variables or usize)
/// let state2 = State::from_iter([v2,v4,v6]);
///
/// assert!(!state.is_active(v0));
/// assert!( state.is_active(v1));
/// assert!(!state.is_active(v2));
/// assert!(!state.is_active(v3));
///
/// // Parse state strings
/// let state3: State = "0010 01100".parse().unwrap();
/// ```
#[cfg_attr(feature = "pyo3", pyclass(module = "bokit"))]
#[derive(Clone, Default, Debug)]
pub struct State {
    active: VarSet,
}

// Functions which are not mapped directly in Python
impl State {
    /// Create a new state without any active variable
    pub fn new() -> Self {
        Self::default()
    }

    /// Iterate over the set of active variables
    pub fn iter_active(&self) -> Iter {
        self.active.iter()
    }

    /// Return the set of active variables
    pub fn into_active(self) -> VarSet {
        self.active
    }
}

#[cfg_attr(feature = "pyo3", pymethods)]
impl State {
    #[cfg(feature = "pyo3")]
    #[new]
    fn new_py(s: Option<&str>) -> PyResult<Self> {
        Ok(match s {
            Some(descr) => State::from_str(descr)?,
            None => State::default(),
        })
    }

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

    /// Get the number of active variables in this state
    ///
    /// Note that the number of inactive variables depends on a separate set of variables
    pub fn len_active(&self) -> usize {
        self.active.len()
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

impl AsRef<VarSet> for State {
    fn as_ref(&self) -> &VarSet {
        &self.active
    }
}

impl AsMut<VarSet> for State {
    fn as_mut(&mut self) -> &mut VarSet {
        &mut self.active
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
        let mut pos = 0;
        for v in self {
            while pos < v.uid() {
                write!(f, "0")?;
                pos += 1;
            }
            write!(f, "1")?;
            pos += 1;
        }
        Ok(())
    }
}
