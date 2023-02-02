//! Solutions to [Advent of Code 2022 Day 20](https://adventofcode.com/2022/day/20).

use std::cmp::Ordering;
use std::io;
use std::num::ParseIntError;

use itertools::Itertools;
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
    let ys = decrypt(xs, 1, 1);
    sum_coordinates(&ys)
}

pub fn solve_part2(xs: &mut [isize]) -> Option<isize> {
    let ys = decrypt(xs, 811_589_153, 10);
    sum_coordinates(&ys)
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

#[must_use]
pub fn decrypt(xs: &[isize], key: isize, rounds: usize) -> Vec<isize> {
    let mut perm: Vec<_> = (0..xs.len()).collect();
    let mut last = vec![0; xs.len()];
    let ys: Vec<_> = xs.iter().map(|&x| x * key).collect();
    match rounds {
        0 => (),
        1 => mix0(&ys, &mut perm, &mut last),
        _ => {
            mix0(&ys, &mut perm, &mut last);
            mix1(&ys, &mut perm, &mut last);
            for _ in 2..rounds {
                mix(&ys, &mut perm, &mut last);
            }
        }
    }
    perm.into_iter().map(|t| ys[t]).collect()
}

/// Applies mixing for round 0.
///
/// Round 0 is special because the permutation is initially the identity.  Sequential elements `t -
/// 1` and `t` are consecutive in the slice `perm`.  Until we get to the iteration on which we move
/// element `t`, it must occur at an index greater than that of where `t - 1` occurs, since on the
/// first round we only shift left as a result of moving earlier elements.
fn mix0(xs: &[isize], perm: &mut [usize], last: &mut [usize]) {
    let n = xs.len();
    let mut previous = 0;
    for (t, &x) in xs.iter().enumerate() {
        let i = perm[previous..]
            .iter()
            .enumerate()
            .find_map(|(i, &s)| if s == t { Some(i + previous) } else { None })
            .unwrap();
        let j = add_mod(i, x, n - 1);
        shift(i, j, perm);
        // We will start searching for `t + 1` where we found `t`.
        previous = i;
        last[t] = j
    }
}

/// Applies mixing for round 1.
///
/// In round 1, for early iterations we find `t` at indices much smaller than `last[t]`.  As `t`
/// increases, the gap between where we find `t` and `last[t]` decreases.  Eventually, for large
/// `t`, we find `t` at indices much larger than `last[t]`.
///
/// Here our strategy is start looking for `t` at `last[t]` adjusted by an offset, where the offset
/// is the actual offset from the previous iteration (i.e., the difference between where we found
/// `t - 1` and `last[t - 1]`).  The actual offset for iteration `t` is then used to predict it for
/// the next iteration.
fn mix1(xs: &[isize], perm: &mut [usize], last: &mut [usize]) {
    let n = xs.len();
    let mut offset = last[0] as isize;
    for (t, &x) in xs.iter().enumerate() {
        let k = (last[t] as isize - offset).max(0).min((n - 1) as isize) as usize;
        let i = perm[k..]
            .iter()
            .enumerate()
            .map(|(i, s)| (i + k, s))
            .interleave(perm[..k].iter().enumerate().rev())
            .find_map(|(i, &s)| if s == t { Some(i) } else { None })
            .unwrap();
        let j = add_mod(i, x, n - 1);
        shift(i, j, perm);
        offset = last[t] as isize - i as isize;
        last[t] = j;
    }
}

/// Applies mixing for rounds n > 1.
///
/// Once the permutation looks random(ish), we just start searching for `t` where we last moved it
/// on the previous round, searching forward and backward in an interleaved fashion.
fn mix(xs: &[isize], perm: &mut [usize], last: &mut [usize]) {
    let n = xs.len();
    for (t, &x) in xs.iter().enumerate() {
        // Find the index where the permutation sends `t`.  We start searching at the index where
        // `t` was moved on the previous round.  Start searching forward and backward interleaved
        // from there.  We unwrap the `Option` because we know `t` is somewhere.
        let k = last[t];
        let i = perm[k..]
            .iter()
            .enumerate()
            .map(|(i, s)| (i + k, s))
            .interleave(perm[..k].iter().enumerate().rev())
            .find_map(|(i, &s)| if s == t { Some(i) } else { None })
            .unwrap();
        let j = add_mod(i, x, n - 1);
        shift(i, j, perm);
        last[t] = j;
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
