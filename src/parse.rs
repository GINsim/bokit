use crate::{error::ParseError, *};
use once_cell::sync::Lazy;
use pest::{iterators, Parser};
use regex::Regex;

#[derive(Parser)]
#[grammar_inline = r####"
expr  = _{ disj }
disj  =  { conj ~ ( "|"  ~ conj )* }
conj  =  { term ~ ( "&" ~ term )* }
term  = _{ neg | grp }
neg   =  { ("!" | "~") ~ grp }
grp   = _{ neg | bt | bf | lit | "(" ~ expr ~ ")" | "[" ~ expr ~ "]" }
bt    =  { ^"true" | "1" }
bf    =  { ^"false" | "0" }
lit   = @{ uid }
value =  { ASCII_DIGIT }
uid   = @{ (ASCII_ALPHA | "_") ~ (ASCII_ALPHANUMERIC | "_")* }

WHITESPACE = _{ " " | "\t" }
"####]
struct ExpressionParser;

static RE_GENERIC_NAME: Lazy<Regex> = Lazy::new(|| Regex::new(r"^\s*_?([01-9]+)_?\s*$").unwrap());

static _NAME_SEPARATORS: [char; 3] = [' ', ',', ';'];

pub trait VariableParser {
    fn parse_variable(&mut self, s: &str) -> Result<Variable, BokitError>;

    fn parse_variable_set(&mut self, s: &str) -> Result<VarSet, BokitError> {
        s.split(&_NAME_SEPARATORS[..])
            .filter(|n| !n.is_empty())
            .map(|n| self.parse_variable(n))
            .collect()
    }

    fn parse_variable_list(&mut self, s: &str) -> Result<VarList, BokitError> {
        let mut result = VarList::default();
        s.split(&_NAME_SEPARATORS[..])
            .filter(|n| !n.is_empty())
            .map(|n| self.parse_variable(n))
            .try_for_each(|v| result.push(v?))?;
        Ok(result)
    }

    /// Parse a state
    fn parse_state(&mut self, s: &str) -> Result<State, BokitError> {
        self.parse_variable_set(s).map(State::from)
    }

    /// Parse a list of implicants with a header line defining a custom variable order
    ///
    /// This method uses a closure to map variable names to actual variables, then
    /// delegates the actual parsing to [Implicants::parse_with_variables].
    fn parse_implicants(&mut self, s: &str) -> Result<Implicants, BokitError> {
        let sep = s.find('\n').ok_or(BokitError::InvalidExpression)?;
        let variables = self.parse_variable_list(&s[..sep])?;
        Implicants::parse_with_variables(&s[sep..], &variables)
    }

    fn parse_expression(&mut self, s: &str) -> Result<Expr, BokitError> {
        let parsed = ExpressionParser::parse(Rule::expr, s);
        if parsed.is_err() {
            return Err(BokitError::InvalidExpression);
        }
        self._load_expr(parsed.unwrap().next().unwrap())
    }

    fn _load_expr(&mut self, expr: iterators::Pair<Rule>) -> Result<Expr, BokitError> {
        let rule = expr.as_rule();
        match rule {
            Rule::bt => Ok(Expr::from(true)),
            Rule::bf => Ok(Expr::from(false)),
            Rule::lit => self.parse_variable(expr.as_str()).map(Expr::from),
            _ => {
                let mut inner = expr.into_inner();
                let mut expr = self._load_expr(inner.next().unwrap())?;
                match rule {
                    Rule::expr => Ok(expr),
                    Rule::neg => Ok(!expr),
                    Rule::conj => loop {
                        match inner.next() {
                            None => return Ok(expr),
                            Some(next) => expr = expr & self._load_expr(next)?,
                        }
                    },
                    Rule::disj => loop {
                        match inner.next() {
                            None => return Ok(expr),
                            Some(next) => expr = expr | self._load_expr(next)?,
                        }
                    },
                    // Other rules are outside of scope or hidden
                    _ => Err(BokitError::InvalidExpression),
                }
            }
        }
    }
}

pub struct BaseVariableParser;

pub fn parser() -> BaseVariableParser {
    BaseVariableParser {}
}

impl VariableParser for BaseVariableParser {
    fn parse_variable(&mut self, s: &str) -> Result<Variable, BokitError> {
        if let Some(cap) = RE_GENERIC_NAME.captures(s) {
            let uid: usize = cap.get(1).unwrap().as_str().parse().unwrap();
            return Ok(Variable::from(uid));
        }
        Err(BokitError::from(ParseError::SimpleParseError(
            s.to_string(),
            "Variable",
        )))
    }
}
