//! Solutions to [Advent of Code 2022 Day 20](https://adventofcode.com/2022/day/20).

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

pub fn parse_input(s: &str) -> Result<Vec<isize>> {
    s.lines()
        .map(|line| line.parse::<isize>().map_err(|e| e.into()))
        .collect()
}

pub fn solve_part1(xs: &mut [isize]) -> Option<isize> {
    mix(xs);
    sum_coordinates(xs)
}

pub fn solve_part2(xs: &mut [isize]) -> Option<isize> {
    decrypt(xs, 811589153, 10);
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
    xs.iter_mut().for_each(|x| *x *= key);
    for _ in 0..rounds {
        mix(xs);
    }
}

pub fn mix(xs: &mut [isize]) {
    let mut perm: Vec<_> = (0..xs.len()).collect();
    let mut inv: Vec<_> = (0..xs.len()).collect();
    for (i, &x) in xs.iter().enumerate() {
        shift(i, x, &mut perm, &mut inv);
    }
    // XXX Rewrite this to work in-place without requiring a separate `ys` vector.
    let ys: Vec<_> = inv.iter().map(|&i| xs[i]).collect();
    xs.iter_mut().zip(ys.into_iter()).for_each(|(x, y)| *x = y);
}

fn shift(index: usize, x: isize, perm: &mut [usize], inv: &mut [usize]) {
    let n = perm.len();
    let i = perm[index];
    let j = add_mod(i, x, n - 1);
    if i < j {
        perm[inv[i]] = j;
        for k in i + 1..=j {
            perm[inv[k]] = k - 1;
        }
        inv[i..=j].rotate_left(1);
    } else if i > j {
        perm[inv[i]] = j;
        for k in j..i {
            perm[inv[k]] = k + 1;
        }
        inv[j..=i].rotate_right(1);
    }
}

/// Computes `(a + x) % m`, where `x` might be negative and `x.abs()` could be larger than `m`.
#[inline]
fn add_mod(a: usize, x: isize, m: usize) -> usize {
    let d = if x >= 0 {
        x as usize
    } else {
        m - ((x.abs() as usize) % m)
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
    fn test_shift() {
        let numbers = vec![1, 2, -3, 3, -2, 0, 4];
        let mut perm: Vec<_> = (0..numbers.len()).collect();
        let mut inv: Vec<_> = (0..numbers.len()).collect();

        shift(0, 1, &mut perm, &mut inv);
        assert_eq!(perm, vec![1, 0, 2, 3, 4, 5, 6]);
        assert_eq!(inv, vec![1, 0, 2, 3, 4, 5, 6]);

        shift(1, 2, &mut perm, &mut inv);
        assert_eq!(perm, vec![0, 2, 1, 3, 4, 5, 6]);
        assert_eq!(inv, vec![0, 2, 1, 3, 4, 5, 6]);

        shift(2, -3, &mut perm, &mut inv);
        assert_eq!(perm, vec![0, 1, 4, 2, 3, 5, 6]);
        assert_eq!(inv, vec![0, 1, 3, 4, 2, 5, 6]);
    }

    #[test]
    fn test_mix() {
        let mut numbers = vec![1, 2, -3, 3, -2, 0, 4];
        mix(&mut numbers);
        assert_eq!(numbers, vec![-2, 1, 2, -3, 4, 0, 3]);
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
        todo!();
    }
}
