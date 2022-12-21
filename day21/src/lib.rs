//! Solutions to [Advent of Code 2022 Day 21](https://adventofcode.com/2022/day/21).

use std::collections::HashMap;
use std::io;
use std::num::ParseIntError;
use std::ops::{Add, Div, Mul, Sub};
use std::str::FromStr;

use once_cell::sync::OnceCell;
use regex::Regex;
use thiserror::Error;

macro_rules! regex {
    ($re:literal $(,)?) => {{
        static RE: OnceCell<Regex> = OnceCell::new();
        RE.get_or_init(|| Regex::new($re).unwrap())
    }};
}

/// The error type for operations in this crate.
#[derive(Debug, Error)]
pub enum Error {
    /// An underlying [`io::Error`].
    #[error("I/O error")]
    Io(#[from] io::Error),

    /// An error parsing an integer.
    #[error("Error parsing integer")]
    ParseInt(#[from] ParseIntError),

    /// An error parsing a named expression.
    #[error("Error parsing named expression: '{0}'")]
    ParseNamedExpression(String),

    /// And error parsing a binary operator: '+', '-', '*', '/'.
    #[error("Error parsing binary operator: '{0}'")]
    ParseOp(String),
}

/// A specialized [`Result`] type for operations in this crate.
///
/// [`Result`]: std::result::Result
pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Subtract,
    Multiply,
    Divide,
}

impl FromStr for BinOp {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        match s {
            "+" => Ok(Self::Add),
            "-" => Ok(Self::Subtract),
            "*" => Ok(Self::Multiply),
            "/" => Ok(Self::Divide),
            _ => Err(Error::ParseOp(s.into())),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expression<T> {
    Simple(T),
    Compound {
        left: String,
        op: BinOp,
        right: String,
    },
}

pub fn parse_input(s: &str) -> Result<HashMap<String, Expression<i64>>> {
    s.lines().map(parse_named_expression).collect()
}

fn parse_named_expression(s: &str) -> Result<(String, Expression<i64>)> {
    let re = regex!(
        r"(?x)
        (?P<name>[[:lower:]]+):\s*
        (
            (?P<num>[[:digit:]]+)
            |
            ( (?P<left>[[:lower:]]+)\s*(?P<op>[+*/-])\s*(?P<right>[[:lower:]]+) )
        )"
    );
    let caps = re
        .captures(s)
        .ok_or_else(|| Error::ParseNamedExpression(s.into()))?;
    let name = caps["name"].to_string();
    let expr = if let Some(digits) = caps.name("num") {
        let num = digits.as_str().parse()?;
        Expression::Simple(num)
    } else {
        let left = caps["left"].to_string();
        let right = caps["right"].to_string();
        let op = caps["op"].parse()?;
        Expression::Compound { left, op, right }
    };
    Ok((name, expr))
}

pub fn eval<T>(expressions: &HashMap<String, Expression<T>>, name: &str) -> Option<T>
where
    T: Copy + Add<Output = T> + Sub<Output = T> + Mul<Output = T> + Div<Output = T>,
{
    let expr = expressions.get(name)?;
    match expr {
        Expression::Simple(t) => Some(*t),
        Expression::Compound { left, op, right } => {
            let a = eval(expressions, left)?;
            let b = eval(expressions, right)?;
            match op {
                BinOp::Add => Some(a + b),
                BinOp::Subtract => Some(a - b),
                BinOp::Multiply => Some(a * b),
                BinOp::Divide => Some(a / b),
            }
        }
    }
}

pub fn solve_part1(expressions: &HashMap<String, Expression<i64>>) -> i64 {
    eval(expressions, "root").expect("the expression can be evaluated")
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_part1_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let exprs = parse_input(&input)?;
        let value = solve_part1(&exprs);
        assert_eq!(value, 152);
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let exprs = parse_input(&input)?;
        let value = solve_part1(&exprs);
        assert_eq!(value, 331120084396440);
        Ok(())
    }

    #[test]
    fn test_part2_example() -> Result<()> {
        todo!();
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        todo!();
    }
}
