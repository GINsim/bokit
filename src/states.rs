use crate::variable::Iter;
use crate::{BokitError, VarSet, Variable};
use std::fmt;
use std::iter::FromIterator;
use std::str::FromStr;

#[cfg(feature = "pyo3")]
use pyo3::{prelude::*, PyObjectProtocol};

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
/// let v0 = Variable::from(0);
/// let v1 = Variable::from(1);
/// let v2 = Variable::from(2);
/// let v3 = Variable::from(3);
/// let v4 = Variable::from(4);
/// let v6 = Variable::from(6);
///
/// let mut state = State::default();
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
    pub(crate) active: VarSet,
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
}

impl State {
    /// Return the inner set of active variables
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

#[cfg(feature = "pyo3")]
#[pyproto]
impl PyObjectProtocol<'_> for State {
    fn __str__(&self) -> String {
        format!("{}", self)
    }
    fn __repr__(&self) -> String {
        format!("{:?}", self)
    }
}
