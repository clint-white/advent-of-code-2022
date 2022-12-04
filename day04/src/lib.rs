//! Solutions to [Advent of Code 2022 Day 4](https://adventofcode.com/2022/day/4)

use std::fs;
use std::io;
use std::num::ParseIntError;
use std::ops::RangeInclusive;
use std::path::Path;

use thiserror::Error;

/// The error type for operations in this crate.
#[derive(Debug, Error)]
pub enum Error {
    /// An underlying [`io::Error`].
    #[error("I/O error")]
    Io(#[from] io::Error),

    /// An error parsing a [`str`] as an integer.
    #[error("Error parsing integer")]
    ParseInt(#[from] ParseIntError),

    /// An input line without a comma-delimited pair of ranges.
    #[error("Line of input missing a comma")]
    BadPair,

    /// An range specified without a `'-'`.
    #[error("Range missing '-'")]
    BadRange,
}

/// A specialized [`Result`] type for operations provided by this crate.
///
/// [`Result`]: std::result::Result
pub type Result<T> = std::result::Result<T, Error>;

/// An extension trait for [`RangeInclusive`].
trait RangeInclusiveExt {
    /// Returns `true` iff `self` is fully contained within `other`.
    fn subset_eq(&self, other: &Self) -> bool;

    /// Returns `true` iff `self` fully contains `other`.
    fn superset_eq(&self, other: &Self) -> bool;

    /// Returns the inclusive range contained within both `self` and `other`.
    #[must_use]
    fn intersection(&self, other: &Self) -> Self;
}

impl<Idx: Ord + Clone> RangeInclusiveExt for RangeInclusive<Idx> {
    fn subset_eq(&self, other: &Self) -> bool {
        self.start() >= other.start() && self.end() <= other.end()
    }

    fn superset_eq(&self, other: &Self) -> bool {
        self.start() <= other.start() && self.end() >= other.end()
    }

    fn intersection(&self, other: &Self) -> Self {
        self.start().max(other.start()).clone()..=self.end().min(other.end()).clone()
    }
}

/// Parses the puzzle input into a list of inclusive range pairs.
///
/// # Examples
///
/// ```
/// use day04::parse_input;
/// # use day04::Error;
///
/// let s = "2-4,6-8
/// 2-3,4-5
/// 5-7,7-9
/// 2-8,3-7
/// 6-6,4-6
/// 2-6,4-8
/// ";
/// let pairs = parse_input(&s)?;
/// let expected = vec![
///     (2..=4, 6..=8),
///     (2..=3, 4..=5),
///     (5..=7, 7..=9),
///     (2..=8, 3..=7),
///     (6..=6, 4..=6),
///     (2..=6, 4..=8),
/// ];
/// assert_eq!(pairs, expected);
/// # Ok::<_, Error>(())
/// ```
///
/// # Errors
///
/// Returns [`enum@Error`] if the input is not a valid list of pairs of ranges.
pub fn parse_input(s: &str) -> Result<Vec<(RangeInclusive<u32>, RangeInclusive<u32>)>> {
    let mut pairs = Vec::new();
    for line in s.lines() {
        let (left, right) = line.split_once(',').ok_or(Error::BadPair)?;
        let left_range = parse_range(left)?;
        let right_range = parse_range(right)?;
        pairs.push((left_range, right_range));
    }
    Ok(pairs)
}

/// Parses an inclusive range in the form `m-n`.
fn parse_range(s: &str) -> Result<RangeInclusive<u32>> {
    let (lower, upper) = s.split_once('-').ok_or(Error::BadRange)?;
    let lower = lower.parse()?;
    let upper = upper.parse()?;
    Ok(lower..=upper)
}

/// Reads the puzzle input from a file and parses it as a list of inclusive range pairs.
///
/// # Errors
///
/// Returns [`enum@Error`] if there were I/O errors reading the input file, or if the input is not
/// a valid list of pairs of ranges.
pub fn read_input<P: AsRef<Path>>(
    path: P,
) -> Result<Vec<(RangeInclusive<u32>, RangeInclusive<u32>)>> {
    let input = fs::read_to_string(path)?;
    parse_input(&input)
}

/// Counts the number of range pairs in which one of the ranges is fully contained in the other.
///
/// # Examples
///
/// ```
/// # use day04::Error;
/// use day04::{parse_input, solve_part1};
///
/// let s = "2-4,6-8
/// 2-3,4-5
/// 5-7,7-9
/// 2-8,3-7
/// 6-6,4-6
/// 2-6,4-8
/// ";
/// let ranges = parse_input(&s)?;
/// let count = solve_part1(&ranges);
/// assert_eq!(count, 2);
/// # Ok::<_, Error>(())
/// ```
#[must_use]
pub fn solve_part1(ranges: &[(RangeInclusive<u32>, RangeInclusive<u32>)]) -> usize {
    ranges
        .iter()
        .filter(|(a, b)| a.subset_eq(b) || (a.superset_eq(b)))
        .count()
}

/// Counts the number of range pairs which have non-empty intersection.
///
/// # Examples
///
/// ```
/// # use day04::Error;
/// use day04::{parse_input, solve_part2};
///
/// let s = "2-4,6-8
/// 2-3,4-5
/// 5-7,7-9
/// 2-8,3-7
/// 6-6,4-6
/// 2-6,4-8
/// ";
/// let ranges = parse_input(&s)?;
/// let count = solve_part2(&ranges);
/// assert_eq!(count, 4);
/// # Ok::<_, Error>(())
/// ```
#[must_use]
pub fn solve_part2(ranges: &[(RangeInclusive<u32>, RangeInclusive<u32>)]) -> usize {
    ranges
        .iter()
        .filter(|(a, b)| !a.intersection(b).is_empty())
        .count()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_part1_input() -> Result<()> {
        let ranges = read_input("data/input")?;
        let count = solve_part1(&ranges);
        assert_eq!(count, 424);
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let ranges = read_input("data/input")?;
        let count = solve_part2(&ranges);
        assert_eq!(count, 804);
        Ok(())
    }
}
