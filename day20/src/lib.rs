//! Solutions to [Advent of Code 2022 Day 20](https://adventofcode.com/2022/day/20).

use std::cmp::Ordering;
use std::io;
use std::num::ParseIntError;

use thiserror::Error;

/// The error type for operations in this crate.
#[derive(Debug, Error)]
pub enum Error {
    /// An underlying [`io::Error`].
    #[error("I/O error")]
    Io(#[from] io::Error),

    /// An error parsing an integer.
    #[error("Error parsing integer")]
    ParseInt(#[from] ParseIntError),
}

/// A specialized [`Result`] type for operations in this crate.
///
/// [`Result`]: std::result::Result
pub type Result<T> = std::result::Result<T, Error>;

/// Parses the input into a vector of integers.
///
/// # Errors
///
/// This function returns an error if any line cannot be parsed as an integer.
pub fn parse_input(s: &str) -> Result<Vec<isize>> {
    s.lines()
        .map(|line| line.parse::<isize>().map_err(Into::into))
        .collect()
}

pub fn solve_part1(xs: &mut [isize]) -> Option<isize> {
    decrypt(xs, 1, 1);
    sum_coordinates(xs)
}

pub fn solve_part2(xs: &mut [isize]) -> Option<isize> {
    decrypt(xs, 811_589_153, 10);
    sum_coordinates(xs)
}

fn sum_coordinates(xs: &[isize]) -> Option<isize> {
    let k = xs
        .iter()
        .enumerate()
        .find_map(|(i, &x)| if x == 0 { Some(i) } else { None })?;
    let n = xs.len();
    let s = xs[(k + 1000) % n] + xs[(k + 2000) % n] + xs[(k + 3000) % n];
    Some(s)
}

pub fn decrypt(xs: &mut [isize], key: isize, rounds: usize) {
    let mut ys: Vec<_> = xs.iter().map(|&x| x * key).enumerate().collect();
    for _ in 0..rounds {
        mix(&mut ys);
    }
    ys.into_iter()
        .map(|(_, y)| y)
        .zip(xs.iter_mut())
        .for_each(|(y, x)| *x = y);
}

fn mix(ys: &mut [(usize, isize)]) {
    let n = ys.len();
    for t in 0..n {
        let (i, &(_, y)) = ys.iter().enumerate().find(|&(_, (s, _))| *s == t).unwrap();
        let j = add_mod(i, y, n - 1);
        shift(i, j, ys);
    }
}

fn shift<T>(i: usize, j: usize, xs: &mut [T]) {
    match i.cmp(&j) {
        Ordering::Less => {
            xs[i..=j].rotate_left(1);
        }
        Ordering::Greater => {
            xs[j..=i].rotate_right(1);
        }
        Ordering::Equal => (),
    }
}

/// Computes `(a + x) % m`, where `x` might be negative and `x.abs()` could be larger than `m`.
#[inline]
fn add_mod(a: usize, x: isize, m: usize) -> usize {
    let d = if x >= 0 {
        x.unsigned_abs()
    } else {
        m - (x.unsigned_abs() % m)
    };
    (a + d) % m
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_mod() {
        assert_eq!(add_mod(1, 3, 6), 4);
        assert_eq!(add_mod(1, -3, 6), 4);
        assert_eq!(add_mod(2, -16, 6), 4);
        assert_eq!(add_mod(4, 20, 11), 2);
        assert_eq!(add_mod(4, -20, 11), 6);
    }

    #[test]
    fn test_mix() {
        let mut ys: Vec<_> = [1, 2, -3, 3, -2, 0, 4].into_iter().enumerate().collect();
        mix(&mut ys);
        let xs: Vec<_> = ys.into_iter().map(|(_, y)| y).collect();
        assert_eq!(xs, vec![-2, 1, 2, -3, 4, 0, 3]);
    }

    #[test]
    fn test_part1_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let mut numbers = parse_input(&input)?;
        let s = solve_part1(&mut numbers);
        assert_eq!(s, Some(3));
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let mut numbers = parse_input(&input)?;
        let s = solve_part1(&mut numbers);
        assert_eq!(s, Some(13289));
        Ok(())
    }

    #[test]
    fn test_part2_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let mut numbers = parse_input(&input)?;
        let s = solve_part2(&mut numbers);
        assert_eq!(s, Some(1623178306));
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let mut numbers = parse_input(&input)?;
        let s = solve_part2(&mut numbers);
        assert_eq!(s, Some(2865721299243));
        Ok(())
    }
}
