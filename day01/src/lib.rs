//! Advent of Code 2022 Day 1

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::io::{self, BufRead};
use std::num::ParseIntError;

use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error("I/O error")]
    Io(#[from] io::Error),

    #[error("Invalid input")]
    Invalid(#[from] ParseIntError),
}

pub type Result<T> = std::result::Result<T, Error>;

/// Parses the input as a vector of vectors.
///
/// # Errors
///
/// Returns [`Error::Io`] if there were errors reading the input.  Returns [`Error::Invalid`] if
/// any of the lines of input cannot be parsed as an `i32`.
pub fn read_input<R: BufRead>(reader: &mut R) -> Result<Vec<Vec<i32>>> {
    let mut chunks = Vec::new();
    let mut current = Vec::new();
    for line in reader.lines() {
        let line = line?;
        if line.is_empty() {
            chunks.push(current);
            current = Vec::new();
        } else {
            current.push(line.parse()?);
        }
    }
    if !current.is_empty() {
        chunks.push(current);
    }
    Ok(chunks)
}

#[must_use]
pub fn max_sum(values: &[Vec<i32>]) -> Option<i32> {
    values.iter().map(|row| row.iter().sum::<i32>()).max()
}

#[must_use]
pub fn sum_topk_sums(values: &[Vec<i32>], k: usize) -> i32 {
    if k == 0 {
        return 0;
    }
    let mut sums = values.iter().map(|row| Reverse(row.iter().sum::<i32>()));
    let mut heap: BinaryHeap<_> = sums.by_ref().take(k).collect();
    for elt in sums {
        let mut root = heap.peek_mut().expect("the heap is nonempty");
        if *root > elt {
            *root = elt;
        }
    }
    heap.into_iter().map(|Reverse(n)| n).sum()
}

#[cfg(test)]
mod tests {
    use std::fs::File;
    use std::io::BufReader;

    use super::*;

    #[test]
    fn part1_example() -> Result<()> {
        let f = File::open("data/example")?;
        let mut reader = BufReader::new(f);
        let values = read_input(&mut reader)?;
        let best = max_sum(&values);
        assert_eq!(best, Some(24000));
        Ok(())
    }

    #[test]
    fn part1_input() -> Result<()> {
        let f = File::open("data/input")?;
        let mut reader = BufReader::new(f);
        let values = read_input(&mut reader)?;
        let best = max_sum(&values);
        assert_eq!(best, Some(75501));
        Ok(())
    }

    #[test]
    fn part2_example() -> Result<()> {
        let f = File::open("data/example")?;
        let mut reader = BufReader::new(f);
        let values = read_input(&mut reader)?;
        let best = sum_topk_sums(&values, 3);
        assert_eq!(best, 45000);
        Ok(())
    }

    #[test]
    fn part2_input() -> Result<()> {
        let f = File::open("data/input")?;
        let mut reader = BufReader::new(f);
        let values = read_input(&mut reader)?;
        let best = sum_topk_sums(&values, 3);
        assert_eq!(best, 215594);
        Ok(())
    }
}
