//! Manipulate sets of (prime) implicants.

use crate::*;
use std::fmt::Display;
use std::iter::FromIterator;
use std::slice::Iter;
use std::str::FromStr;
use std::vec::IntoIter;

pub(crate) static PATTERN_SEPARATORS: [char; 4] = [',', ';', '|', '\n'];

/// Boolean function represented as a set of implicants.
///
/// An implicant of a Boolean function is a pattern such that the function is true for all covered states.
/// The implicants in a set of implicants cover exactly all true states of the function.
#[derive(Clone, Default, Debug)]
pub struct ImplicantSet {
    patterns: Vec<Pattern>,
}

impl ImplicantSet {
    fn with(patterns: Vec<Pattern>) -> Self {
        Self { patterns }
    }

    pub fn iter(&self) -> Iter<'_, Pattern> {
        self.patterns.iter()
    }

    /// Remove all patterns.
    ///
    /// This will give an empty set, covering the FALSE function
    pub fn clear(&mut self) {
        self.patterns.clear();
    }

    /// Keep only the implicants matching the provided condition.
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&Pattern) -> bool,
    {
        self.patterns.retain(f);
    }

    /// Extract a subset of the implicants into a separate set, retain only the others implicants
    pub(crate) fn split_subset<F>(&mut self, mut f: F) -> Self
    where
        F: FnMut(&Pattern) -> bool,
    {
        // TODO: use drain_filter (when it is stable) to avoid cloning
        let to_extract: Vec<Pattern> = self.patterns.iter().filter(|p| f(p)).cloned().collect();
        self.patterns.retain(|p| !f(p));
        Self::with(to_extract)
    }

    /// Add a restriction to all implicants in the set.
    ///
    /// Note that this may introduce conflicts for some implicants
    pub fn restrict(&mut self, uid: usize, value: bool) {
        for p in &mut self.patterns {
            p.set_ignoring_conflicts(uid, value);
        }
    }

    /// Add all patterns from another set
    pub fn append(&mut self, other: &mut Self) {
        self.patterns.append(&mut other.patterns)
    }

    /// Test if the given pattern is covered by at least one pattern in this set.
    ///
    /// Note that if it returns false, the states of the target pattern could still be contained in
    /// this list of implicants. This corner case is eliminated if the implicants are prime.
    pub fn contains(&self, p: &Pattern) -> bool {
        self.iter().any(|t| t.contains(p))
    }

    /// Remove all patterns covered by at least one pattern of the given set
    pub fn exclude(&mut self, other: &Self) {
        self.patterns.retain(|p| !other.contains(p));
    }

    /// Find the patterns emerging from two sets of patterns.
    ///
    /// These emerging pattern cover states of the two sets and are not contained in any of them
    pub fn emerging(&self, other: &Self) -> Self {
        let mut result = ImplicantSet::default();

        for p in &self.patterns {
            for t in &other.patterns {
                if let Some(e) = p.emerging_pattern(t) {
                    // TODO: if e contains p (resp t) testing self (resp other) is not needed
                    if self.contains(&e) || other.contains(&e) {
                        continue;
                    }
                    result.push_new_pattern(e);
                }
            }
        }

        result
    }

    /// Add a new pattern avoiding duplicate.
    ///
    /// If the new pattern is contained in the set, nothing changes.
    /// Otherwise, the newly subsumed patterns are removed from the set.
    pub fn push_new_pattern(&mut self, p: Pattern) {
        if self.contains(&p) {
            return;
        }
        self.retain(|t| !p.contains(t));
        self.patterns.push(p);
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

impl FromIterator<Pattern> for ImplicantSet {
    fn from_iter<I: IntoIterator<Item = Pattern>>(iter: I) -> Self {
        let mut implicants = ImplicantSet::default();
        for p in iter {
            implicants.push_new_pattern(p);
        }
        implicants
    }
}

impl<'a> IntoIterator for &'a ImplicantSet {
    type Item = &'a Pattern;
    type IntoIter = Iter<'a, Pattern>;

    fn into_iter(self) -> Self::IntoIter {
        self.patterns.iter()
    }
}

impl IntoIterator for ImplicantSet {
    type Item = Pattern;
    type IntoIter = IntoIter<Pattern>;

    fn into_iter(self) -> Self::IntoIter {
        self.patterns.into_iter()
    }
}

impl FromStr for ImplicantSet {
    type Err = BokitError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut result = ImplicantSet::default();
        for elt in s.split(&PATTERN_SEPARATORS[..]) {
            result.push_new_pattern(elt.parse()?);
        }
        Ok(result)
    }
}

impl Rule for ImplicantSet {
    fn fmt_rule(&self, f: &mut fmt::Formatter, _namer: &VariableCollection) -> fmt::Result {
        self.fmt(f)
    }

    fn eval(&self, state: &State) -> bool {
        self.patterns.iter().any(|p| p.contains_state(state))
    }

    fn collect_regulators(&self, regulators: &mut VarSet) {
        for p in &self.patterns {
            regulators.union_with(&p.positive);
            regulators.union_with(&p.negative);
        }
    }
}

impl fmt::Display for ImplicantSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for p in &self.patterns {
            writeln!(f, "{}", p)?;
        }
        write!(f, "")
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

        let is1: ImplicantSet = "--01-1---0-1".parse().unwrap();
        assert_eq!(is1.patterns.len(), 1);

        let is2 = "--01-1\n1-0101\n--0-1".parse::<ImplicantSet>().unwrap();
        assert_eq!(is2.patterns.len(), 2);

        let implicants: ImplicantSet = "0-10;0-11;1-11".parse().unwrap();
        assert_eq!(implicants.len(), 3);
    }
}
