use crate::*;
use std::borrow::Cow;

use crate::implicants::covers_slice;
use crate::tools::quick_partition;
use std::iter::FromIterator;
use std::slice::Iter;
use std::str::FromStr;
use std::vec::IntoIter;

use crate::efmt::ExprFormatter;
use crate::expr::{ExprNode, Operator};
use crate::variable::VariableCounter;
#[cfg(feature = "pyo3")]
use pyo3::{exceptions::PyValueError, prelude::*};

/// Boolean function represented as a set of prime implicants.
///
/// This is a special case of [`Implicants`].
/// An implicant is "prime" if it is not contained in any other implicant.
/// A set of prime implicants is a set of implicant containg all prime implicants.
#[cfg_attr(feature = "pyo3", pyclass(module = "bokit"))]
#[derive(Clone, Debug, Default)]
pub struct Primes {
    patterns: Implicants,
}

#[cfg_attr(feature = "pyo3", pymethods)]
impl Primes {
    #[cfg(feature = "pyo3")]
    #[new]
    fn new_py(arg: Option<&PyAny>) -> PyResult<Self> {
        match arg {
            None => Ok(Primes::from(false)),
            Some(obj) => extract_primes(obj),
        }
    }

    #[cfg(feature = "pyo3")]
    #[pyo3(name = "eval")]
    fn eval_py(&self, state: &State) -> bool {
        self.eval(state)
    }

    /// Get the number of patterns in this list of prime implicants
    pub fn len(&self) -> usize {
        self.patterns.len()
    }

    /// Return whether there are no prime implicant (the rule is always false)
    pub fn is_empty(&self) -> bool {
        self.patterns.is_empty()
    }

    /// Check if this function is true in at least one state of the given pattern
    pub fn satisfiable_in_pattern(&self, pattern: &Pattern) -> bool {
        self.patterns.satisfiable_in_pattern(pattern)
    }

    /// Add a restriction on a single variable to this set of prime implicants.
    ///
    /// This will perform the following operations:
    /// 1) remove the patterns which would have conflicts
    /// 2) extract the unchanged patterns
    /// 3) Update all remaining patterns
    /// 4) remove newly subsumed patterns
    pub fn restrict(&mut self, uid: Variable, value: bool) {
        // Add the restriction, eliminate conflicts and separate unchanged patterns
        let pivot = self.patterns.restrict(uid, value);

        // If no or all implicants have changed, we are done
        if pivot == 0 || pivot == self.len() {
            return;
        }

        // Exclude the restricted implicants (after pivot) that could be subsumed by unchanged ones (before pivot)
        let (slice_unchanged, slice_restricted) = self.patterns.as_mut_slice().split_at_mut(pivot);
        let end = quick_partition(slice_restricted, |p| !covers_slice(slice_unchanged, p));
        self.patterns.truncate(pivot + end);

        unsafe {
            // Here it is safe to clear the subsumed flag
            self.patterns.clear_subsumed_flag();
        }
    }

    /// Merge two lists of prime implicants.
    ///
    /// Patterns subsumed in any of the lists are removed
    /// Emerging patterns are identified and lead to recursive merge until no new emerging pattern is found
    pub fn merge(&mut self, other: &mut Self) {
        // remove subsumed patterns from the two sets
        self.patterns.exclude(&other.patterns);
        other.patterns.exclude(&self.patterns);

        // Generate the set of emerging patterns
        let emerging = self.patterns.emerging(&other.patterns);

        self.patterns.append(&mut other.patterns);

        // Recursive call to a private function to merge the emerging patterns
        self.merge_emerging(emerging);

        unsafe {
            // Here it is safe to clear the subsumed flag
            self.patterns.clear_subsumed_flag();
        }
    }

    pub fn add_pattern(&mut self, p: Pattern) {
        // TODO: add a faster implementation for common easy cases?
        let mut other = Primes::default();
        other.patterns.push_clear_subsumed(p);
        self.merge(&mut other);
    }

    #[cfg(feature = "pyo3")]
    fn __str__(&self) -> String {
        format!("{}", self)
    }

    #[cfg(feature = "pyo3")]
    fn __repr__(&self) -> String {
        format!("{}", self)
    }
}

impl Primes {
    pub fn parse_with_variables(descr: &str, variables: &VarList) -> Result<Self, BokitError> {
        Ok(Primes::from(Implicants::parse_with_variables(
            descr, variables,
        )?))
    }

    pub fn into_implicants(self) -> Implicants {
        self.patterns
    }

    pub fn as_implicants(&self) -> &Implicants {
        &self.patterns
    }

    fn merge_emerging(&mut self, mut emerging: Implicants) {
        if emerging.is_empty() {
            return;
        }
        self.patterns.exclude(&emerging);

        let mut next_emerging = self.patterns.emerging(&emerging);
        let mut self_emerging = emerging.emerging(&emerging);
        next_emerging.append(&mut self_emerging);

        self.patterns.append(&mut emerging);

        self.merge_emerging(next_emerging);
    }

    pub fn from_expr(expr: &Expr) -> Self {
        let mut result = Self::from(true);
        result._expand_expr(expr, true);
        result
    }

    fn _expand_expr(&mut self, expr: &Expr, value: bool) {
        match &expr.node {
            ExprNode::Variable(var) => self.restrict(*var, expr.value == value),
            ExprNode::True => {
                if expr.value != value {
                    self.patterns.clear();
                }
            }
            ExprNode::Pattern(p) => match expr.value == value {
                true => self._expand_and_pattern(p),
                false => self._expand_or_pattern(p),
            },
            ExprNode::Operation(op, children) => match (expr.value == value, op) {
                (true, Operator::And) => self._expand_and(children, true),
                (false, Operator::Or) => self._expand_and(children, false),
                (true, Operator::Or) => self._expand_or(children, true),
                (false, Operator::And) => self._expand_or(children, false),
            },
        }
    }

    fn _expand_and(&mut self, children: &(Expr, Expr), value: bool) {
        self._expand_expr(&children.0, value);
        self._expand_expr(&children.1, value);
    }

    fn _expand_or(&mut self, children: &(Expr, Expr), value: bool) {
        let mut other = self.clone();
        self._expand_expr(&children.0, value);
        other._expand_expr(&children.1, value);
        self.merge(&mut other);
    }

    fn _expand_and_pattern(&mut self, pattern: &Pattern) {
        // TODO: apply all restrictions at once (and loose some optimizations in corner cases)
        pattern
            .positive
            .iter()
            .for_each(|var| self.restrict(var, true));
        pattern
            .negative
            .iter()
            .for_each(|var| self.restrict(var, false));
    }

    fn _expand_or_merge(&mut self, original: &mut Option<Self>, var: Variable, value: bool) {
        match original {
            None => {
                *original = Some(self.clone());
                self.restrict(var, value);
            }
            Some(ori) => {
                let mut p = ori.clone();
                p.restrict(var, value);
                self.merge(&mut p);
            }
        }
    }

    fn _expand_or_pattern(&mut self, p: &Pattern) {
        let mut original = None;
        p.positive
            .iter()
            .for_each(|var| self._expand_or_merge(&mut original, var, false));
        p.negative
            .iter()
            .for_each(|var| self._expand_or_merge(&mut original, var, true));
    }
}

#[cfg(feature = "pyo3")]
fn extract_primes(obj: &PyAny) -> PyResult<Primes> {
    if let Ok(e) = obj.extract::<'_, Primes>() {
        return Ok(e);
    }
    if let Ok(e) = obj.extract::<'_, Implicants>() {
        return Ok(Primes::from(e));
    }
    if let Ok(e) = obj.extract::<'_, Variable>() {
        return Ok(Primes::from(e));
    }
    if let Ok(e) = obj.extract::<'_, bool>() {
        return Ok(Primes::from(e));
    }
    if let Ok(e) = obj.extract::<'_, &str>() {
        return Ok(e.parse()?);
    }
    if let Ok(e) = obj.extract::<'_, Expr>() {
        return Ok(Primes::from(e));
    }
    Err(PyValueError::new_err(format!(
        "'{}' can not be converted to 'Expr'",
        obj.get_type().name()?
    )))
}

impl FromIterator<Pattern> for Primes {
    fn from_iter<I: IntoIterator<Item = Pattern>>(iter: I) -> Self {
        let mut primes = Primes::default();
        for p in iter {
            primes.add_pattern(p);
        }
        primes
    }
}

impl<T: Into<Pattern>> From<T> for Primes {
    fn from(pattern: T) -> Self {
        Primes::from(Implicants::from(pattern))
    }
}

impl<'a> IntoIterator for &'a Primes {
    type Item = &'a Pattern;
    type IntoIter = Iter<'a, Pattern>;

    fn into_iter(self) -> Self::IntoIter {
        self.patterns.iter()
    }
}

impl IntoIterator for Primes {
    type Item = Pattern;
    type IntoIter = IntoIter<Pattern>;

    fn into_iter(self) -> Self::IntoIter {
        self.patterns.into_iter()
    }
}

impl FromStr for Primes {
    type Err = BokitError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Primes::from(s.parse::<Implicants>()?))
    }
}

impl Rule for Primes {
    fn fmt_with(&self, f: &mut dyn ExprFormatter) -> fmt::Result {
        self.patterns.fmt_with(f)
    }

    fn eval(&self, state: &State) -> bool {
        self.patterns.eval(state)
    }

    fn collect_regulators(&self, regulators: &mut VarSet) {
        self.patterns.collect_regulators(regulators);
    }

    fn count_regulators(&self, regulators: &mut VariableCounter, value: bool) {
        self.patterns.count_regulators(regulators, value)
    }

    fn as_expression(&self) -> Cow<Expr> {
        Cow::Owned(Expr::from(self))
    }

    fn as_implicants(&self) -> Cow<Implicants> {
        Cow::Borrowed(&self.patterns)
    }

    fn as_primes(&self) -> Cow<Primes> {
        Cow::Borrowed(self)
    }
}

// delegate Display impl to the implicant set
impl fmt::Display for Primes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.patterns.fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn test_basics() -> Result<(), BokitError> {
        let pi = Primes::from(false);
        assert_eq!(pi.len(), 0);

        let mut pi = Primes::from(true);
        assert_eq!(pi.len(), 1);
        let p: &Pattern = &pi.patterns[0];
        assert_eq!(p.positive.len(), 0);
        assert_eq!(p.negative.len(), 0);

        pi.restrict(Variable(2), true);
        assert_eq!(pi.len(), 1);
        let p: &Pattern = &pi.patterns[0];
        assert_eq!(p.positive.len(), 1);
        assert_eq!(p.negative.len(), 0);

        Ok(())
    }

    #[test]
    fn count_primes() -> Result<(), BokitError> {
        let mut variables = VarSpace::default();
        let first = variables.provide("first")?;
        let test = variables.provide("test")?;
        let other = variables.provide("other")?;
        let myvar = variables.provide("myvar")?;

        let e: Expr = (test | other) & true & ((!myvar | first) & test);

        let primes = Primes::from(&e);

        assert_eq!(2, primes.len());

        let e: Expr = (test & other) | (myvar & other & !test) | (test & !myvar & other);
        let primes = Primes::from(&e);
        assert_eq!(2, primes.len());

        let v1 = Variable::from(1);
        let v2 = Variable::from(2);
        let v3 = Variable::from(3);
        let v4 = Variable::from(4);
        let v5 = Variable::from(5);
        let v6 = Variable::from(6);
        let v7 = Variable::from(7);
        let v8 = Variable::from(8);
        let v9 = Variable::from(9);
        let v10 = Variable::from(10);

        let e: Expr = ((v1 | v2) & (v3 | v4) & v5) | (v6 & (v7 | v8)) | (v9 & v10);
        let primes = Primes::from(&e);
        assert_eq!(7, primes.patterns.len());

        Ok(())
    }

    #[test]
    fn convert() {
        let implicants: Implicants = "0-10;0-11;1-11".parse().unwrap();

        let primes1 = Primes::from(&implicants);

        let expr = Expr::from(&implicants);

        let primes2 = Primes::from(&expr);

        assert_eq!(implicants.len(), 3);
        assert_eq!(primes1.len(), 2);
        assert_eq!(primes2.len(), 2);
    }
}
