use crate::*;
use pest::{iterators, Parser};

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

pub fn parse_expression(
    f: &mut dyn FnMut(&str) -> Result<Variable, BokitError>,
    text: &str,
) -> Result<Expr, BokitError> {
    let parsed = ExpressionParser::parse(Rule::expr, text);
    if parsed.is_err() {
        return Err(BokitError::InvalidExpression);
    }
    load_expr(f, parsed.unwrap().next().unwrap())
}

fn load_expr(
    f: &mut dyn FnMut(&str) -> Result<Variable, BokitError>,
    expr: iterators::Pair<Rule>,
) -> Result<Expr, BokitError> {
    let rule = expr.as_rule();
    match rule {
        Rule::bt => Ok(Expr::from(true)),
        Rule::bf => Ok(Expr::from(false)),
        Rule::lit => f(expr.as_str()).map(Expr::from),
        _ => {
            let mut inner = expr.into_inner();
            let mut expr = load_expr(f, inner.next().unwrap())?;
            match rule {
                Rule::expr => Ok(expr),
                Rule::neg => Ok(!expr),
                Rule::conj => loop {
                    match inner.next() {
                        None => return Ok(expr),
                        Some(next) => expr = expr & load_expr(f, next)?,
                    }
                },
                Rule::disj => loop {
                    match inner.next() {
                        None => return Ok(expr),
                        Some(next) => expr = expr | load_expr(f, next)?,
                    }
                },
                // Other rules are outside of scope or hidden
                _ => Err(BokitError::InvalidExpression),
            }
        }
    }
}
