//! Formatting API for expressions

use crate::{Operator, Pattern, Rule, VarSpace, Variable};
use delegate::delegate;

use std::fmt;

pub struct FormatterConfig<'a> {
    s_and: &'a str,
    s_or: &'a str,
    s_not: &'a str,
}

pub static DEFAULT_FMT_CFG: FormatterConfig = FormatterConfig {
    s_and: "&",
    s_or: "|",
    s_not: "!",
};

pub static LOWERCASE_FMT_CFG: FormatterConfig = FormatterConfig {
    s_and: " and ",
    s_or: " or ",
    s_not: "not ",
};

pub struct InfixFormatted<'a, T: Rule> {
    rule: &'a T,
    cfg: &'a FormatterConfig<'a>,
    ovs: Option<&'a VarSpace>,
}

/// Define hooks to display separate parts of expressions.
///
/// This trait provide entry points used by [crate::Expr::fmt_with] to control the presentation of the expression.
/// The expression visits the inner tree and calls the hooks defined in this trait for each node and leaf.
///
/// A default formatter is implemented on top of [fmt::Formatter], additional formatters are used through
/// Rule wrappers overriding the Display trait.
pub trait ExprFormatter {
    /// Pass-through function calling an internal [fmt::Formatter].
    ///
    /// This function enables the use of the ```write!``` macro in other functions.
    fn write_fmt(&mut self, args: fmt::Arguments) -> fmt::Result;

    /// Write a fixed Boolean node
    fn write_bool(&mut self, b: bool) -> fmt::Result;

    /// Write a single variable, which can be negated
    fn write_variable(&mut self, var: Variable, value: bool) -> fmt::Result;

    /// Start writing an operation
    ///
    /// Note that this function is not called for identical nested operation
    fn start_operation(
        &mut self,
        op: Operator,
        value: bool,
        parent: Option<Operator>,
    ) -> fmt::Result;

    /// Stop writing an operation
    ///
    /// Note that this function is not called for identical nested operation
    fn end_operation(&mut self, op: Operator, value: bool, parent: Option<Operator>)
        -> fmt::Result;

    /// Separate operands in the ongoing operation
    ///
    /// This is called between the two children and before each nested identical operation.
    fn sep_operation(&mut self, op: Operator) -> fmt::Result;

    /// Write a full pattern
    ///
    /// In absence of specialized operation, this functions emulate a set of operations joining the variables in the pattern.
    fn write_pattern(&mut self, p: &Pattern, value: bool, parent: Option<Operator>) -> fmt::Result {
        if p.is_free_pattern() {
            return self.write_bool(value);
        }

        let op = match value {
            true => Operator::And,
            false => Operator::Or,
        };

        self.start_operation(op, true, parent)?;
        let mut first = true;
        for (var, val) in p.iter_fixed_values() {
            match first {
                true => first = false,
                false => self.sep_operation(op)?,
            }
            self.write_variable(var, val == value)?;
        }
        self.end_operation(op, true, parent)
    }
}

impl FormatterConfig<'_> {
    pub fn operator(&self, op: Operator) -> &str {
        match op {
            Operator::And => self.s_and,
            Operator::Or => self.s_or,
        }
    }

    pub fn infix<'a, T: Rule>(
        &'a self,
        rule: &'a T,
        vs: Option<&'a VarSpace>,
    ) -> InfixFormatted<'a, T> {
        InfixFormatted {
            rule,
            ovs: vs,
            cfg: self,
        }
    }
}

pub struct InfixFormatter<'a, 'b>(
    &'a mut fmt::Formatter<'b>,
    Option<&'a VarSpace>,
    &'a FormatterConfig<'a>,
);
pub struct PrefixFormatter<'a, 'b>(InfixFormatter<'a, 'b>);

impl<'a, 'b> InfixFormatter<'a, 'b> {
    pub fn new(f: &'a mut fmt::Formatter<'b>) -> Self {
        Self(f, None, &DEFAULT_FMT_CFG)
    }
    pub fn named(f: &'a mut fmt::Formatter<'b>, vs: &'a VarSpace) -> Self {
        Self(f, Some(vs), &DEFAULT_FMT_CFG)
    }
    pub fn with(
        f: &'a mut fmt::Formatter<'b>,
        ovs: Option<&'a VarSpace>,
        cfg: &'a FormatterConfig,
    ) -> Self {
        Self(f, ovs, cfg)
    }
}

impl<'a, 'b> PrefixFormatter<'a, 'b> {
    pub fn new(f: &'a mut fmt::Formatter<'b>) -> Self {
        Self(InfixFormatter::new(f))
    }
    pub fn named(f: &'a mut fmt::Formatter<'b>, vs: &'a VarSpace) -> Self {
        Self(InfixFormatter::named(f, vs))
    }
}

impl ExprFormatter for InfixFormatter<'_, '_> {
    fn write_fmt(&mut self, args: fmt::Arguments) -> fmt::Result {
        fmt::Formatter::write_fmt(self.0, args)
    }

    fn write_bool(&mut self, b: bool) -> fmt::Result {
        match b {
            false => write!(self, "0"),
            true => write!(self, "1"),
        }
    }

    fn write_variable(&mut self, var: Variable, value: bool) -> fmt::Result {
        if !value {
            write!(self, "{}", self.2.s_not)?;
        }
        match self.1 {
            None => write!(self, "_{}_", var),
            Some(vs) => vs.format_variable(self.0, var),
        }
    }

    fn start_operation(
        &mut self,
        op: Operator,
        value: bool,
        parent: Option<Operator>,
    ) -> fmt::Result {
        match value {
            false => write!(self, "{}(", self.2.s_not),
            true => match op.priority() < parent.map(|o| o.priority()).unwrap_or(0) {
                true => write!(self, "("),
                false => Ok(()),
            },
        }
    }

    fn end_operation(
        &mut self,
        op: Operator,
        value: bool,
        parent: Option<Operator>,
    ) -> fmt::Result {
        match value {
            false => write!(self, ")"),
            true => match op.priority() < parent.map(|o| o.priority()).unwrap_or(0) {
                true => write!(self, ")"),
                false => Ok(()),
            },
        }
    }

    fn sep_operation(&mut self, op: Operator) -> fmt::Result {
        write!(self, " {} ", self.2.operator(op))
    }
}

pub struct PrefixFormatted<'a, R: Rule>(pub &'a R);

impl<'a, R: Rule> fmt::Display for PrefixFormatted<'a, R> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut ef = PrefixFormatter::new(f);
        self.0.fmt_with(&mut ef)
    }
}

impl<T: Rule> fmt::Display for InfixFormatted<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut ef = InfixFormatter::with(f, self.ovs, self.cfg);
        self.rule.fmt_with(&mut ef)
    }
}

impl ExprFormatter for PrefixFormatter<'_, '_> {
    delegate! {
        to self.0 {
            fn write_fmt(&mut self, args: fmt::Arguments) -> fmt::Result;
            fn write_bool(&mut self, b: bool) -> fmt::Result;
            fn write_variable(&mut self, var: Variable, value: bool) -> fmt::Result;
        }
    }

    fn start_operation(
        &mut self,
        op: Operator,
        value: bool,
        _parent: Option<Operator>,
    ) -> fmt::Result {
        if !value {
            write!(self, "!")?;
        }
        match op {
            Operator::And => write!(self, "(& "),
            Operator::Or => write!(self, "(| "),
        }
    }

    fn end_operation(
        &mut self,
        _op: Operator,
        _value: bool,
        _parent: Option<Operator>,
    ) -> fmt::Result {
        write!(self, ")")
    }

    fn sep_operation(&mut self, _op: Operator) -> fmt::Result {
        write!(self, " ")
    }
}

#[cfg(test)]
mod tests {
    use crate::efmt;
    use crate::parse::VariableParser;
    use crate::*;

    #[test]
    fn extract_variable() -> Result<(), BokitError> {
        let mut vs = VarSpace::default();
        let expr = vs.extend().parse_expression("A | (B & C)")?;
        let e1 = vs.extend().parse_expression("A | B & C")?;
        let e2 = vs.extend().parse_expression("A & (B | C)")?;
        let e3 = vs.extend().parse_expression("A & B | C")?;

        println!("{}", &expr);
        println!("{}", &e1);
        println!("{}", &e2);
        println!("{}", &e3);

        println!();
        println!("NAMED: {}", vs.named(&expr));

        let expr = vs.extend().parse_expression("A & (D | (!C | B))")?;
        let fr = efmt::PrefixFormatted(&expr);
        println!("prefixed: {}", &fr);

        Ok(())
    }
}
