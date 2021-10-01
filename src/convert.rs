use crate::{Expr, Implicants, Pattern, Primes, SomeRule, Variable};
use std::borrow::Cow;

impl From<&Implicants> for Expr {
    fn from(patterns: &Implicants) -> Expr {
        patterns
            .iter()
            .fold(Expr::from(false), |expr, p| expr | Expr::from(p))
    }
}

impl From<&Primes> for Expr {
    fn from(primes: &Primes) -> Self {
        Self::from(primes.as_implicants())
    }
}

impl From<Primes> for Implicants {
    fn from(primes: Primes) -> Self {
        primes.into_implicants()
    }
}

impl From<&Primes> for Implicants {
    fn from(primes: &Primes) -> Self {
        primes.as_implicants().clone()
    }
}

impl From<&Implicants> for Primes {
    fn from(implicants: &Implicants) -> Self {
        implicants.clone().into()
    }
}

impl From<Implicants> for Primes {
    fn from(implicants: Implicants) -> Self {
        // TODO: improve the conversion of implicants to primes
        let mut result = Self::default();
        implicants.into_iter().for_each(|p| result.add_pattern(p));
        result
    }
}

impl From<&Expr> for Primes {
    fn from(expr: &Expr) -> Self {
        Self::from_expr(expr)
    }
}
impl From<Expr> for Primes {
    fn from(expr: Expr) -> Self {
        Self::from_expr(&expr)
    }
}

impl From<&Expr> for Implicants {
    fn from(expr: &Expr) -> Self {
        Primes::from(expr).into()
    }
}
impl From<Expr> for Implicants {
    fn from(expr: Expr) -> Self {
        Primes::from(&expr).into()
    }
}

impl From<bool> for Implicants {
    fn from(value: bool) -> Self {
        let mut result = Self::default();
        if value {
            result.push_clear_subsumed(Pattern::default());
        }
        result
    }
}

impl From<bool> for Primes {
    fn from(value: bool) -> Self {
        Primes::from(Implicants::from(value))
    }
}

impl From<Expr> for SomeRule {
    fn from(e: Expr) -> Self {
        SomeRule::Expr(e)
    }
}
impl From<Implicants> for SomeRule {
    fn from(i: Implicants) -> Self {
        SomeRule::Implicants(i)
    }
}
impl From<Primes> for SomeRule {
    fn from(p: Primes) -> Self {
        SomeRule::Primes(p)
    }
}
impl From<Variable> for SomeRule {
    fn from(v: Variable) -> Self {
        SomeRule::Expr(v.into())
    }
}
impl From<bool> for SomeRule {
    fn from(b: bool) -> Self {
        SomeRule::from(Expr::from(b))
    }
}

impl From<&SomeRule> for Expr {
    fn from(rule: &SomeRule) -> Self {
        match rule {
            SomeRule::Expr(e) => e.clone(),
            SomeRule::Primes(p) => p.into(),
            SomeRule::Implicants(i) => i.into(),
        }
    }
}

impl From<&SomeRule> for Implicants {
    fn from(rule: &SomeRule) -> Self {
        match rule {
            SomeRule::Expr(e) => Self::from(e),
            SomeRule::Primes(p) => Self::from(p),
            SomeRule::Implicants(i) => i.clone(),
        }
    }
}

impl From<&SomeRule> for Primes {
    fn from(rule: &SomeRule) -> Self {
        match rule {
            SomeRule::Expr(e) => Self::from(e),
            SomeRule::Primes(p) => p.clone(),
            SomeRule::Implicants(i) => Self::from(i),
        }
    }
}

impl<'a> From<&'a SomeRule> for Cow<'a, Expr> {
    fn from(rule: &'a SomeRule) -> Self {
        match rule {
            SomeRule::Expr(b) => Cow::Borrowed(b),
            _ => Cow::Owned(Expr::from(rule)),
        }
    }
}

impl<'a> From<&'a SomeRule> for Cow<'a, Primes> {
    fn from(rule: &'a SomeRule) -> Self {
        match rule {
            SomeRule::Primes(b) => Cow::Borrowed(b),
            _ => Cow::Owned(Primes::from(rule)),
        }
    }
}

impl<'a> From<&'a SomeRule> for Cow<'a, Implicants> {
    fn from(rule: &'a SomeRule) -> Self {
        match rule {
            SomeRule::Implicants(b) => Cow::Borrowed(b),
            SomeRule::Primes(b) => Cow::Borrowed(b.as_implicants()),
            _ => Cow::Owned(Implicants::from(rule)),
        }
    }
}
