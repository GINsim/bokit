//! Manipulate sets of (prime) implicants.

use crate::*;
use bit_set::BitSet;
use std::fmt::Display;
use std::iter::FromIterator;
use std::ops::{Index, IndexMut, Range};
use std::slice::Iter;
use std::str::FromStr;
use std::vec::IntoIter;

#[cfg(feature = "pyo3")]
use pyo3::{exceptions::PyValueError, prelude::*, PyObjectProtocol};

pub(crate) static PATTERN_SEPARATORS: [char; 4] = [',', ';', '|', '\n'];

/// Boolean function represented as a set of implicants.
///
/// An implicant of a Boolean function is a pattern such that the function is true for all covered states.
/// The implicants in a set of implicants covering exactly all true states of the function.
///
/// The list keeps track of the potential for some implicants to be contained in others.
#[cfg_attr(feature = "pyo3", pyclass(module = "bokit"))]
#[derive(Clone, Default, Debug)]
pub struct Implicants {
    patterns: Vec<Pattern>,
    /// Track whether this list could contains subsumed patterns
    subsumed_flag: bool,
}

impl Implicants {
    /// Create a new, empty list of implicants.
    pub fn new() -> Self {
        Self::default()
    }

    /// Import a list of patterns as a list of implicants.
    /// If it contains at least two patterns, it will be tainted for potential subsumed patterns.
    fn with(patterns: Vec<Pattern>) -> Self {
        let mut result = Self {
            patterns,
            subsumed_flag: true,
        };
        result.reset_subsumed_flag();

        result
    }

    /// Parse a list of implicants with a header line defining a custom variable order
    ///
    /// This method uses a closure to map variable names to actual variables, then
    /// delegates the actual parsing to [Self::parse_with_variables].
    pub fn parse_with_header<F: FnMut(&str) -> Result<Variable, BokitError>>(
        descr: &str,
        f: F,
    ) -> Result<Self, BokitError> {
        let sep = descr.find('\n').ok_or(BokitError::InvalidExpression)?;
        let variables = VarList::parse(&descr[..sep], f)?;
        Self::parse_with_variables(&descr[sep..], &variables)
    }

    /// Parse a list of implicants using a custom variable order
    pub fn parse_with_variables(descr: &str, variables: &VarList) -> Result<Self, BokitError> {
        split_patterns(descr)
            .map(|p| Pattern::parse_with_variables(p, variables))
            .collect()
    }

    pub fn iter(&self) -> Iter<'_, Pattern> {
        self.patterns.iter()
    }

    /// Force clearing the subsumed flag, use with extra care.
    ///
    /// The subsumed flag is used to avoid searching for subsumed implicants to remove
    /// when we already know that the list does not contain any of them.
    /// The flag is enabled for lists containing at least two implicants (see [Self::reset_subsumed_flag]).
    /// If the subsumed flag is cleared in a list containing subsumed patterns, a call
    /// to remove subsumed pattern will return early and leave the subsumed patterns in place.
    ///
    /// # Safety
    ///
    /// This function is memory safe, but can compromise the consistency of the list.
    /// In most cases, the subsumed flag is enabled when new patterns are added and cleared when subsumed
    /// patterns are removed (see [Self::clear_subsumed_patterns] and [Self::push_clear_subsumed]).
    ///
    /// In some cases (for example in a [list of primes implicants](Primes)), the subsumed flag is
    /// set to ensure consistency, but additional context continues to ensure their absence.
    /// This function is then useful to avoid unnecessary computations in the future.
    pub unsafe fn clear_subsumed_flag(&mut self) {
        self.subsumed_flag = false;
    }

    /// Set the subsumed flag if the list contains several patterns
    pub fn reset_subsumed_flag(&mut self) {
        self.subsumed_flag = self.len() > 1;
    }

    /// Keep only implicants matching the provided condition.
    ///
    /// It does not affect the subsumed flag but may affect the order of the remaining implicants.
    /// It uses [Self::quick_partition] to group all removed items then truncates the list.
    ///
    /// The subsumed flag can be cleared if the list if reduced to less than 2 implicants.
    pub fn quick_retain<F: Fn(&Pattern) -> bool>(&mut self, f: F) {
        let pivot = self.quick_partition(f);
        if pivot < self.len() {
            self.patterns.truncate(pivot);
            self.subsumed_flag &= self.len() > 1;
        }
    }

    /// Split the list according to a condition.
    ///
    /// It uses a "quick-sort-like" approach with low and high indices which are used to swap as few
    ///elements as possible.
    /// Returns the pivot index such that all items satisfying f are in ```self[0..pivot]```.
    pub fn quick_partition<F: Fn(&Pattern) -> bool>(&mut self, f: F) -> usize {
        tools::quick_partition(&mut self.patterns, f)
    }

    /// Get full access to the inner data
    ///
    /// The [subsumed flag is reset](Self::reset_subsumed_flag) as it enables any modification.
    pub fn as_mut_slice(&mut self) -> &mut [Pattern] {
        self.reset_subsumed_flag();
        self.patterns.as_mut_slice()
    }

    pub fn range_covers(&self, range: Range<usize>, p: &Pattern) -> bool {
        self.patterns[range].iter().any(|t| t.contains(p))
    }

    /// Find the patterns emerging from two sets of patterns.
    ///
    /// These emerging pattern cover states of the two sets and are not contained in any of them
    pub fn emerging(&self, other: &Self) -> Self {
        let mut result = Implicants::default();

        for p in &self.patterns {
            for t in &other.patterns {
                if let Some(e) = p.emerging_pattern(t) {
                    // TODO: if e contains p (resp t) testing self (resp other) is not needed
                    if self.covers(&e) || other.covers(&e) {
                        continue;
                    }
                    result.push_clear_subsumed(e);
                }
            }
        }

        result
    }

    pub fn collect_regulators_range(&self, start: usize, end: usize, vars: &mut VarSet) {
        self.patterns[start..end]
            .iter()
            .for_each(|p| p.collect_regulators(vars));
    }

    /// Remove a selection of the patterns.
    pub fn filtered_patterns(&mut self, selection: &BitSet) {
        // TODO: can we remove this function?

        if selection.is_empty() {
            return;
        }
        let mut index = 0;
        self.patterns.retain(|_| {
            index += 1;
            !selection.contains(index - 1)
        })
    }

    pub fn truncate(&mut self, end: usize) {
        self.patterns.truncate(end)
    }

    /// Swap two elements in the list of patterns.
    ///
    /// Can be used to partition the list in place.
    pub fn swap(&mut self, a: usize, b: usize) {
        self.patterns.swap(a, b)
    }

    /// Remove a pattern and replace it with the last one
    pub fn swap_remove(&mut self, index: usize) -> Pattern {
        self.patterns.swap_remove(index)
    }
}

#[cfg_attr(feature = "pyo3", pymethods)]
impl Implicants {
    #[cfg(feature = "pyo3")]
    #[new]
    fn new_py(arg: Option<&PyAny>) -> PyResult<Self> {
        match arg {
            None => Ok(Implicants::from(false)),
            Some(obj) => extract_implicants(obj),
        }
    }

    #[cfg(feature = "pyo3")]
    #[pyo3(name = "eval")]
    fn eval_py(&self, state: &State) -> bool {
        self.eval(state)
    }

    /// Return the subsumed flag.
    ///
    /// When this flag is false, the list should not contain any pair of pattern subsuming each other.
    pub fn subsumed_flag(&self) -> bool {
        self.subsumed_flag
    }

    /// Restrict this list of implicants to a given subspace.
    ///
    /// If the subspace does not fix any regulator of this list of implicant, then nothing changes.
    /// Otherwise, the patterns conflicting with the subspace are removed, and the remaining patterns
    /// are simplified to eliminate unnecessary fixed variables.
    ///
    /// In absence of conflicting variable in the subspace, we obtain the non-empty intersections of patterns with
    /// the subspace. A conflicting variable in the subspace is considered as a conflict if it fixed at any value
    /// in an implicant, but the implicants where it does not appear remain valid.
    /// The resulting function evaluates to true if it is satisfied without the conflicting variables.
    pub fn restrict_to_subspace(&mut self, fixed: &Pattern) {
        let regulators = self.get_regulators();
        if regulators.is_disjoint(&fixed.positive) && regulators.is_disjoint(&fixed.negative) {
            return;
        }

        self.quick_retain(|p| p.overlaps(fixed));
        self.patterns
            .iter_mut()
            .for_each(|p| p.restrict_ignore_conflicts(fixed));
        // TODO: the subsumed flag is cleared to be safe, can we preserve it?
        self.subsumed_flag &= self.len() > 1;
    }

    /// Remove all patterns.
    ///
    /// The resulting empty list corresponds to the FALSE function
    /// The flag for potentially subsumed patterns is also cleared
    pub fn clear(&mut self) {
        self.patterns.clear();
        self.subsumed_flag = false;
    }

    /// Add a restriction to all implicants in the set.
    ///
    /// Patterns which had an opposite restriction are considered as conflicts and removed.
    /// Patterns which had the same restriction remain unchanged and grouped at the start of the list.
    /// As a result the order of the remaining implicants can be changed.
    ///
    /// The subsumed flag is enforced if the pivot separates two non-empty sublists.
    pub fn restrict(&mut self, uid: Variable, value: bool) -> usize {
        // Start by removing all conflicting patterns
        let not_value = !value;
        self.quick_retain(|p| !p.has_restriction(uid, not_value));

        // Group the unchanged patterns at the start of the list
        let pivot = self.quick_partition(|p| p.has_restriction(uid, value));

        // Apply the restriction to the remaining patterns
        self.patterns[pivot..]
            .iter_mut()
            .for_each(|p| p.set_ignoring_conflicts(uid, value));
        self.subsumed_flag |= pivot > 0 && pivot < self.len();
        pivot
    }

    /// Add all patterns from another set.
    ///
    /// The subsumed flag is set either if the two lists are not empty
    /// or if it was previously set in at least one of them.
    pub fn append(&mut self, other: &mut Self) {
        self.patterns.append(&mut other.patterns);
        self.subsumed_flag |= other.subsumed_flag || (!self.is_empty() && !other.is_empty());
    }

    /// Test if the given pattern is covered by at least one pattern in this set.
    ///
    /// Note that if it returns false, the states of the target pattern could still be
    /// contained in this list of implicants, even for prime implicants.
    pub fn covers(&self, p: &Pattern) -> bool {
        self.range_covers(0..self.len(), p)
    }

    /// Remove all patterns covered by at least one pattern of the given set.
    ///
    /// Does not affect the subsumed flag.
    pub fn exclude(&mut self, other: &Self) {
        match other.len() {
            0 => (),
            1 => {
                let o = &other[0];
                self.quick_retain(|p| !o.contains(p));
            }
            _ => {
                // TODO: use summaries to speed it up
                // let vars = other.get_regulators();
                self.quick_retain(|p| !other.covers(p));
            }
        }
    }

    /// Add a pattern to the list
    ///
    /// The pattern is added without any consistency check: it could already be in the list,
    /// or contained in an existing pattern, or contain some existing patterns.
    /// See [Self::push_clear_subsumed] for a more restrictive addition
    pub fn push(&mut self, p: Pattern) {
        self.subsumed_flag |= !self.is_empty();
        self.patterns.push(p)
    }

    /// Add a new pattern avoiding duplicate.
    ///
    /// If the new pattern is contained in the set, nothing changes.
    /// Otherwise, any newly subsumed patterns are removed from the set before adding the new pattern.
    pub fn push_clear_subsumed(&mut self, p: Pattern) {
        if self.covers(&p) {
            return;
        }
        self.quick_retain(|t| !p.contains(t));
        self.patterns.push(p);
    }

    /// Remove all patterns contained in at least one other pattern of the list.
    pub fn clear_subsumed_patterns(&mut self) {
        // Do nothing if this list is already clean
        if !self.subsumed_flag {
            return;
        }

        // TODO: use drain on a range or at least swap_remove as we go
        let mut filtered = BitSet::new();
        for idx in 0..self.len() {
            if filtered.contains(idx) {
                continue;
            }
            let p = &self.patterns[idx];
            for idx2 in idx + 1..self.len() {
                if filtered.contains(idx2) {
                    continue;
                }
                let p2 = &self.patterns[idx2];
                if p2.contains(p) {
                    filtered.insert(idx);
                    break;
                }
                if p.contains(p2) {
                    filtered.insert(idx2);
                }
            }
        }
        self.filtered_patterns(&filtered);
        self.subsumed_flag = false;
    }

    /// Check if this function is true in at least one state of the given pattern
    pub fn satisfiable_in_pattern(&self, pattern: &Pattern) -> bool {
        self.patterns.iter().any(|p| p.overlaps(pattern))
    }

    /// Get the number of patterns in this list of implicants
    pub fn len(&self) -> usize {
        self.patterns.len()
    }

    /// Return whether there are no implicant (the rule is always false)
    pub fn is_empty(&self) -> bool {
        self.patterns.is_empty()
    }
}

#[cfg(feature = "pyo3")]
fn extract_implicants(obj: &PyAny) -> PyResult<Implicants> {
    if let Ok(e) = obj.extract::<'_, Implicants>() {
        return Ok(e);
    }
    if let Ok(e) = obj.extract::<'_, Variable>() {
        return Ok(Implicants::from(e));
    }
    if let Ok(e) = obj.extract::<'_, bool>() {
        return Ok(Implicants::from(e));
    }
    if let Ok(e) = obj.extract::<'_, &str>() {
        return Ok(e.parse()?);
    }
    if let Ok(e) = obj.extract::<'_, Expr>() {
        return Ok(Implicants::from(e));
    }
    Err(PyValueError::new_err(format!(
        "'{}' can not be converted to 'Expr'",
        obj.get_type().name()?
    )))
}

pub fn covers_slice(slice: &[Pattern], p: &Pattern) -> bool {
    slice.iter().any(|t| t.contains(p))
}

impl Index<usize> for Implicants {
    type Output = Pattern;

    fn index(&self, index: usize) -> &Self::Output {
        self.patterns.index(index)
    }
}

impl IndexMut<usize> for Implicants {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.subsumed_flag = true;
        self.patterns.index_mut(index)
    }
}

impl FromIterator<Pattern> for Implicants {
    fn from_iter<I: IntoIterator<Item = Pattern>>(iter: I) -> Self {
        Implicants::with(Vec::from_iter(iter))
    }
}

impl<'a> IntoIterator for &'a Implicants {
    type Item = &'a Pattern;
    type IntoIter = Iter<'a, Pattern>;

    fn into_iter(self) -> Self::IntoIter {
        self.patterns.iter()
    }
}

impl IntoIterator for Implicants {
    type Item = Pattern;
    type IntoIter = IntoIter<Pattern>;

    fn into_iter(self) -> Self::IntoIter {
        self.patterns.into_iter()
    }
}

fn split_patterns(s: &str) -> impl Iterator<Item = &str> {
    s.split(&PATTERN_SEPARATORS[..])
        .filter(|p| !p.trim().is_empty())
}

impl FromStr for Implicants {
    type Err = BokitError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        split_patterns(s).map(|p| p.parse()).collect()
    }
}

impl<T: Into<Pattern>> From<T> for Implicants {
    fn from(pattern: T) -> Self {
        let mut implicants = Implicants::default();
        implicants.push_clear_subsumed(pattern.into());
        implicants
    }
}

impl Rule for Implicants {
    fn fmt_rule(&self, f: &mut fmt::Formatter, _namer: &VarSpace) -> fmt::Result {
        self.fmt(f)
    }

    fn eval(&self, state: &State) -> bool {
        self.patterns.iter().any(|p| p.contains_state(state))
    }

    fn collect_regulators(&self, regulators: &mut VarSet) {
        self.patterns
            .iter()
            .for_each(|p| p.collect_regulators(regulators));
    }
}

impl fmt::Display for Implicants {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for p in &self.patterns {
            writeln!(f, "{}", p)?;
        }
        write!(f, "")
    }
}

#[cfg(feature = "pyo3")]
#[pyproto]
impl PyObjectProtocol<'_> for Implicants {
    fn __str__(&self) -> String {
        format!("{}", self)
    }
    fn __repr__(&self) -> String {
        format!("{}", self)
    }
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn parsing() {
        let p: Pattern = "--01-1---0-1".parse().unwrap();
        assert_eq!(p.positive.len(), 3);
        assert_eq!(p.negative.len(), 2);

        let is1: Implicants = "--01-1---0-1".parse().unwrap();
        assert_eq!(is1.patterns.len(), 1);

        let mut is2 = "--01-1\n1-0101\n--0-1".parse::<Implicants>().unwrap();
        assert_eq!(is2.patterns.len(), 3);

        is2.clear_subsumed_patterns();
        assert_eq!(is2.patterns.len(), 2);

        let implicants: Implicants = "0-10;0-11;1-11".parse().unwrap();
        assert_eq!(implicants.len(), 3);
    }

    #[test]
    fn restrict_subspace() -> Result<(), BokitError> {
        let ipl: Implicants = "0-- ; --1 ; 10-".parse()?;

        let mut sub = Pattern::default();
        sub.set(Variable(1), false);

        let mut r = ipl.clone();
        r.restrict_to_subspace(&sub);
        assert_eq!(r.len(), 3);
        assert_eq!(&r[0], &ipl[0]);
        assert_eq!(&r[1], &ipl[1]);
        let p = "1--".parse::<Pattern>()?;
        assert_eq!(&r[2], &p);

        sub.set(Variable(2), false);
        r = ipl.clone();
        r.restrict_to_subspace(&sub);
        assert_eq!(r.len(), 2);
        assert_eq!(&r[0], &ipl[0]);
        assert_eq!(&r[1], &p);

        Ok(())
    }
}
