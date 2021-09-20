use crate::*;

use crate::implicants::PATTERN_SEPARATORS;
use std::iter::FromIterator;
use std::slice::Iter;
use std::str::FromStr;
use std::vec::IntoIter;

/// Boolean function represented as a set of prime implicants.
///
/// This is a special case of ImplicantSet.
/// An implicant is "prime" if it is not contained in any other implicant.
/// A set of prime implicants is a set of implicant containg all prime implicants.
#[derive(Clone, Debug, Default)]
pub struct Primes {
    patterns: ImplicantSet,
}

impl Primes {
    /// Get the number of patterns in this list of prime implicants
    pub fn len(&self) -> usize {
        self.patterns.len()
    }

    /// Return whether there are no prime implicant (the rule is always false)
    pub fn is_empty(&self) -> bool {
        self.patterns.is_empty()
    }

    pub fn as_implicants(&self) -> &ImplicantSet {
        &self.patterns
    }

    pub fn into_implicants(self) -> ImplicantSet {
        self.patterns
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
    pub fn restrict(&mut self, uid: usize, value: bool) {
        // Start by removing all conflicting patterns
        self.patterns.retain(|p| !p.has_restriction(uid, !value));

        // Extract the unchanged patterns and keep only the extended ones
        let mut unchanged = self
            .patterns
            .split_subset(|p| p.has_restriction(uid, value));

        // Apply the restriction to the remaining patterns
        self.patterns.restrict(uid, value);

        // Eliminate newly subsumed patterns
        self.patterns.exclude(&unchanged);

        // merge back the two sets
        self.patterns.append(&mut unchanged);
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
    }

    pub fn add_pattern(&mut self, p: Pattern) {
        // TODO: add a faster implementation for common easy cases?
        let mut other = Primes::default();
        other.patterns.push_new_pattern(p);
        self.merge(&mut other);
    }

    fn merge_emerging(&mut self, mut emerging: ImplicantSet) {
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

    fn _expand_expr(&mut self, expr: &Expr, positive: bool) {
        match expr {
            Expr::Atom(uid) => self.restrict(uid.uid(), positive),
            Expr::Not(e) => self._expand_expr(e, !positive),
            Expr::Bool(b) => {
                if *b != positive {
                    self.patterns.clear();
                }
            }
            Expr::Operation(op, children) => match (positive, op) {
                (true, Operator::And) => self._expand_and(children, positive),
                (false, Operator::Or) => self._expand_and(children, positive),
                (true, Operator::Or) => self._expand_or(children, positive),
                (false, Operator::And) => self._expand_or(children, positive),
            },
        }
    }

    fn _expand_and(&mut self, children: &(Expr, Expr), positive: bool) {
        self._expand_expr(&children.0, positive);
        self._expand_expr(&children.1, positive);
    }

    fn _expand_or(&mut self, children: &(Expr, Expr), positive: bool) {
        let mut other = self.clone();
        self._expand_expr(&children.0, positive);
        other._expand_expr(&children.1, positive);
        self.merge(&mut other);
    }
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
        let mut result = Primes::default();
        for elt in s.split(&PATTERN_SEPARATORS[..]) {
            result.add_pattern(elt.parse()?);
        }
        Ok(result)
    }
}

impl Rule for Primes {
    fn fmt_rule(&self, f: &mut fmt::Formatter, namer: &VariableCollection) -> fmt::Result {
        self.patterns.fmt_rule(f, namer)
    }

    fn eval(&self, state: &State) -> bool {
        self.patterns.eval(state)
    }

    fn collect_regulators(&self, regulators: &mut VarSet) {
        self.patterns.collect_regulators(regulators);
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
    fn count_primes() -> Result<(), BokitError> {
        let mut variables = VariableCollection::default();
        let first = variables.add("first")?;
        let test = variables.add("test")?;
        let other = variables.add("other")?;
        let myvar = variables.add("myvar")?;

        let e: Expr = (test | other) & true & ((!myvar | first) & test);

        let primes = Primes::from(&e);

        assert_eq!(2, primes.patterns.len());

        let e: Expr = (test & other) | (myvar & other & !test) | (test & !myvar & other);
        let primes = Primes::from(&e);
        assert_eq!(2, primes.patterns.len());

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
        let implicants: ImplicantSet = "0-10;0-11;1-11".parse().unwrap();

        let primes1 = Primes::from(&implicants);

        let expr = Expr::from(&implicants);

        let primes2 = Primes::from(&expr);

        assert_eq!(implicants.len(), 3);
        assert_eq!(primes1.len(), 2);
        assert_eq!(primes2.len(), 2);
    }
}
