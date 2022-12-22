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
    Sub,
    Mul,
    Div,
}

impl FromStr for BinOp {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        match s {
            "+" => Ok(Self::Add),
            "-" => Ok(Self::Sub),
            "*" => Ok(Self::Mul),
            "/" => Ok(Self::Div),
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
                BinOp::Sub => Some(a - b),
                BinOp::Mul => Some(a * b),
                BinOp::Div => Some(a / b),
            }
        }
    }
}

pub fn solve_part1(expressions: &HashMap<String, Expression<i64>>) -> i64 {
    eval(expressions, "root").expect("the expression can be evaluated")
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolicExpression<T> {
    Constant(T),
    Variable(&'static str),
    Operation {
        left: Box<SymbolicExpression<T>>,
        op: BinOp,
        right: Box<SymbolicExpression<T>>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Equation<T>(SymbolicExpression<T>, SymbolicExpression<T>);

/// Returns a symbolic equation by converting a binary operation expression for `node` into an
/// equality.
pub fn build_equation<T>(
    expressions: &HashMap<String, Expression<T>>,
    node: &str,
) -> Option<Equation<T>>
where
    T: Copy + Add<Output = T> + Sub<Output = T> + Mul<Output = T> + Div<Output = T>,
{
    let expr = expressions.get(node)?;
    match expr {
        // If the node is a simple expression, return no equation.
        Expression::Simple(_) => None,
        // If the node is a binary operation, convert it into an equality between the two sides of
        // the operator.
        Expression::Compound { left, op: _, right } => {
            let lhs = build_symbolic_expression(expressions, left)?;
            let rhs = build_symbolic_expression(expressions, right)?;
            Some(Equation(lhs, rhs))
        }
    }
}

/// Build a symbolic expression where the expression for node `humn` is converted to a variable.
pub fn build_symbolic_expression<T>(
    expressions: &HashMap<String, Expression<T>>,
    node: &str,
) -> Option<SymbolicExpression<T>>
where
    T: Copy + Add<Output = T> + Sub<Output = T> + Mul<Output = T> + Div<Output = T>,
{
    if node == "humn" {
        return Some(SymbolicExpression::Variable("x"));
    };
    let expr = expressions.get(node)?;
    let symb_expr = match expr {
        Expression::Simple(num) => SymbolicExpression::Constant(*num),
        Expression::Compound { left, op, right } => {
            let a = build_symbolic_expression(expressions, left)?;
            let b = build_symbolic_expression(expressions, right)?;
            match (a, b) {
                (SymbolicExpression::Constant(a), SymbolicExpression::Constant(b)) => match op {
                    BinOp::Add => SymbolicExpression::Constant(a + b),
                    BinOp::Sub => SymbolicExpression::Constant(a - b),
                    BinOp::Mul => SymbolicExpression::Constant(a * b),
                    BinOp::Div => SymbolicExpression::Constant(a / b),
                },
                (a, b) => SymbolicExpression::Operation {
                    left: Box::new(a),
                    op: *op,
                    right: Box::new(b),
                },
            }
        }
    };
    Some(symb_expr)
}

pub fn reduce<T>(equation: Equation<T>) -> Equation<T>
where
    T: Copy + Add<Output = T> + Sub<Output = T> + Mul<Output = T> + Div<Output = T>,
{
    use SymbolicExpression::{Constant, Operation};

    match (equation.0, equation.1) {
        (Operation { left, op, right }, Constant(c)) => rewrite(*left, op, *right, c),
        (Constant(a), Constant(b)) => Equation(Constant(a), Constant(b)),
        (Constant(a), rhs) => reduce(Equation(rhs, Constant(a))),
        (lhs, rhs) => Equation(lhs, rhs),
    }
}

pub fn rewrite<T>(
    left: SymbolicExpression<T>,
    op: BinOp,
    right: SymbolicExpression<T>,
    c: T,
) -> Equation<T>
where
    T: Copy + Add<Output = T> + Sub<Output = T> + Mul<Output = T> + Div<Output = T>,
{
    use SymbolicExpression::{Constant, Operation};
    match (left, right) {
        (Constant(a), Constant(b)) => match op {
            BinOp::Add => Equation(Constant(a + b), Constant(c)),
            BinOp::Sub => Equation(Constant(a - b), Constant(c)),
            BinOp::Mul => Equation(Constant(a * b), Constant(c)),
            BinOp::Div => Equation(Constant(a / b), Constant(c)),
        },
        (Constant(a), rhs) => match op {
            BinOp::Add => Equation(rhs, Constant(c - a)),
            BinOp::Sub => Equation(rhs, Constant(a - c)),
            BinOp::Mul => Equation(rhs, Constant(c / a)),
            BinOp::Div => Equation(
                Constant(a),
                Operation {
                    left: Box::new(rhs),
                    op: BinOp::Mul,
                    right: Box::new(Constant(c)),
                },
            ),
        },
        (lhs, Constant(b)) => match op {
            BinOp::Add => Equation(lhs, Constant(c - b)),
            BinOp::Sub => Equation(lhs, Constant(c + b)),
            BinOp::Mul => Equation(lhs, Constant(c / b)),
            BinOp::Div => Equation(lhs, Constant(c * b)),
        },
        (lop, rop) => Equation(
            Operation {
                left: Box::new(lop),
                op,
                right: Box::new(rop),
            },
            Constant(c),
        ),
    }
}

pub fn solve_part2(expressions: &HashMap<String, Expression<i64>>) -> Option<i64> {
    let mut eqn = build_equation(expressions, "root").unwrap();
    while !matches!(&eqn.0, SymbolicExpression::Variable(_)) {
        eqn = reduce(eqn);
    }
    match eqn.1 {
        SymbolicExpression::Constant(t) => Some(t),
        _ => None,
    }
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
        let input = fs::read_to_string("data/example")?;
        let exprs = parse_input(&input)?;
        let ans = solve_part2(&exprs);
        assert_eq!(ans, Some(301));
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let exprs = parse_input(&input)?;
        let ans = solve_part2(&exprs);
        assert_eq!(ans, Some(3378273370680));
        Ok(())
    }
}
