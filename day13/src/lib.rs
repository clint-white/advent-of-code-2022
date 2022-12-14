//! Solutions to [Advent of Code 2022 Day 13](https://adventofcode.com/2022/day/13).

use std::cmp::Ordering;
use std::io;

use thiserror::Error;

/// The error type for operations in this crate.
#[derive(Debug, Error)]
pub enum Error {
    /// An underlying [`io::Error`].
    #[error("I/O error")]
    Io(#[from] io::Error),

    /// Unexpected end of input
    #[error("Unexpected end of input")]
    UnexpectedEndOfInput,

    /// Parse error
    #[error("Parse error")]
    Parse,
}

/// A specialized [`Result`] type for operations in this crate.
///
/// [`Result`]: std::result::Result
pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tree<T> {
    Leaf(T),
    Branch(Vec<Tree<T>>),
}

impl<T: Ord> Ord for Tree<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Tree::Leaf(a), Tree::Leaf(b)) => a.cmp(b),
            (Tree::Branch(xs), Tree::Branch(ys)) => xs.cmp(ys),
            (leaf, Tree::Branch(ys)) => {
                if let Some((y, rest)) = ys.split_first() {
                    leaf.cmp(y).then_with(|| {
                        if rest.is_empty() {
                            Ordering::Equal
                        } else {
                            Ordering::Less
                        }
                    })
                } else {
                    Ordering::Greater
                }
            }
            (Tree::Branch(xs), leaf) => {
                if let Some((x, rest)) = xs.split_first() {
                    x.cmp(leaf).then_with(|| {
                        if rest.is_empty() {
                            Ordering::Equal
                        } else {
                            Ordering::Greater
                        }
                    })
                } else {
                    Ordering::Less
                }
            }
        }
    }
}

impl<T: Ord> PartialOrd for Tree<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[must_use]
pub fn solve_part1(pairs: &[(Tree<i32>, Tree<i32>)]) -> usize {
    pairs
        .iter()
        .enumerate()
        .filter_map(|(i, (left, right))| if left <= right { Some(i + 1) } else { None })
        .sum()
}

#[must_use]
pub fn solve_part2(pairs: Vec<(Tree<i32>, Tree<i32>)>) -> usize {
    let divider2 = Tree::Branch(vec![Tree::Leaf(2)]);
    let divider6 = Tree::Branch(vec![Tree::Leaf(6)]);
    let mut packets = vec![divider2.clone(), divider6.clone()];
    for (left, right) in pairs {
        packets.push(left);
        packets.push(right);
    }
    packets.sort();
    packets
        .iter()
        .enumerate()
        .filter_map(|(i, packet)| {
            if packet == &divider2 || packet == &divider6 {
                Some(i + 1)
            } else {
                None
            }
        })
        .product()
}

pub use parser::parse_input;

mod parser {
    use nom::{
        branch::alt,
        character::complete::{char, digit1, newline},
        combinator::{all_consuming, map, map_res},
        multi::separated_list0,
        sequence::{delimited, terminated, tuple},
        IResult,
    };

    use super::{Error, Result, Tree};

    pub fn parse_input(s: &str) -> Result<Vec<(Tree<i32>, Tree<i32>)>> {
        let (_, values) = all_consuming(parse_pairs)(s).map_err(|_| Error::Parse)?;
        Ok(values)
    }

    fn parse_pairs(s: &str) -> IResult<&str, Vec<(Tree<i32>, Tree<i32>)>> {
        separated_list0(newline, parse_pair)(s)
    }

    fn parse_pair(s: &str) -> IResult<&str, (Tree<i32>, Tree<i32>)> {
        tuple((
            terminated(parse_tree, newline),
            terminated(parse_tree, newline),
        ))(s)
    }

    fn parse_tree(s: &str) -> IResult<&str, Tree<i32>> {
        alt((parse_leaf, parse_branch))(s)
    }

    fn parse_leaf(s: &str) -> IResult<&str, Tree<i32>> {
        map(parse_integer, Tree::Leaf)(s)
    }

    fn parse_branch(s: &str) -> IResult<&str, Tree<i32>> {
        map(
            delimited(char('['), parse_children, char(']')),
            Tree::Branch,
        )(s)
    }

    fn parse_children(s: &str) -> IResult<&str, Vec<Tree<i32>>> {
        separated_list0(char(','), parse_tree)(s)
    }

    fn parse_integer(s: &str) -> IResult<&str, i32> {
        map_res(digit1, str::parse)(s)
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_part1_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let pairs = parse_input(&input)?;
        let index_sum = solve_part1(&pairs);
        assert_eq!(index_sum, 13);
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let pairs = parse_input(&input)?;
        let index_sum = solve_part1(&pairs);
        assert_eq!(index_sum, 5503);
        Ok(())
    }

    #[test]
    fn test_part2_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let pairs = parse_input(&input)?;
        let index_sum = solve_part2(pairs);
        assert_eq!(index_sum, 140);
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let pairs = parse_input(&input)?;
        let index_sum = solve_part2(pairs);
        assert_eq!(index_sum, 20952);
        Ok(())
    }
}
