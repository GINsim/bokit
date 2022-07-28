use crate::Variable;
use thiserror::Error;

#[cfg(feature = "pyo3")]
use pyo3::{exceptions::PyValueError, PyErr};
use std::num::{ParseFloatError, ParseIntError};

/// Error in the name of a variable.
#[derive(Error, Debug)]
pub enum BokitError {
    /// The name is invalid
    #[error("The name '{0}' is invalid")]
    InvalidName(String),

    /// The name Conflicts
    #[error("The name '{0}' conflicts with an other variable")]
    ConflictingName(String),

    /// The name is not part of the set of variables
    #[error("There is no variable named '{0}'")]
    NoSuchVariableName(String),

    /// The variable is not part of the group
    #[error("There is no variable '{0}' in this group")]
    NoSuchVariable(Variable),

    /// The expression is invalid
    #[error("Not a valid expression")]
    InvalidExpression,

    /// Parsing error
    #[error("Parse error: {0}")]
    ParseError(ParseError),
}

#[derive(Error, Debug)]
pub enum ParseError {
    /// Simple mismatch
    #[error("The string '{0}' could not be parsed as '{1}'")]
    SimpleParseError(String, &'static str),

    /// Parse error without a description
    #[error("Undefined parse error")]
    JustError,
}

#[cfg(feature = "pyo3")]
impl From<BokitError> for PyErr {
    fn from(e: BokitError) -> Self {
        // TODO: better conversion to Python errors
        PyValueError::new_err(format!("{}", e))
    }
}

impl From<ParseError> for BokitError {
    fn from(e: ParseError) -> Self {
        Self::ParseError(e)
    }
}

impl From<ParseIntError> for BokitError {
    fn from(_: ParseIntError) -> Self {
        Self::InvalidExpression
    }
}

impl From<ParseFloatError> for BokitError {
    fn from(_: ParseFloatError) -> Self {
        Self::InvalidExpression
    }
}

impl<T> From<pest::error::Error<T>> for BokitError {
    fn from(_: pest::error::Error<T>) -> Self {
        Self::InvalidExpression
    }
}
