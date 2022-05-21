use crate::{Expr, Implicants, Pattern, Primes};

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
