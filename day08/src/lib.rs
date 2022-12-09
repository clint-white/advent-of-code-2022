//! Solutions to [Advent of Code 2022 Day 8](https://adventofcode.com/2022/day/8).

use std::io;

use thiserror::Error;

use ndarray::ShapeError;
pub use ndarray::{Array2, ArrayView2};

/// The error type for operations in this crate.
#[derive(Debug, Error)]
pub enum Error {
    /// An underlying [`io::Error`].
    #[error("I/O error")]
    Io(#[from] io::Error),

    /// Error parsing input characters.
    #[error("Invalid byte: {0}")]
    Parse(u8),

    /// Inconsistent row lengths
    #[error("Inconsistent row lengths: {0}, {1}")]
    InconsistentRowLengths(usize, usize),

    /// Shape error
    #[error("An error related to the shape of the array")]
    ShapeError(#[from] ShapeError),
}

/// A specialized [`Result`] type for operations in this crate.
///
/// [`Result`]: std::result::Result
pub type Result<T> = std::result::Result<T, Error>;

/// Parses puzzle input into a two dimensional array.
///
/// # Errors
///
/// This function will return an error if it cannot parse the input into a two-dimensional array of
/// ascii digits.  This may include characters other than ascii digits, or rows of unequal lengths.
pub fn parse_input(s: &str) -> Result<Array2<u8>> {
    let mut data = Vec::new();
    let mut ncols = None;
    let mut nrows = 0;
    for line in s.lines() {
        nrows += 1;
        let bytes = line.trim().as_bytes();
        if let Some(n) = ncols {
            if bytes.len() != n {
                return Err(Error::InconsistentRowLengths(bytes.len(), n));
            }
        } else {
            ncols = Some(bytes.len());
        }

        let result: Result<Vec<_>> = bytes
            .iter()
            .map(|&c| {
                if c.is_ascii_digit() {
                    Ok(c - b'0')
                } else {
                    Err(Error::Parse(c))
                }
            })
            .collect();
        let row = result?;
        data.extend(row);
    }
    let array = Array2::from_shape_vec((nrows, ncols.unwrap_or(0)), data)?;
    Ok(array)
}

/// Returns an iterator yielding the positions and values of new maxima in a sequence.
fn prefix_argmax<I, T>(values: I) -> impl Iterator<Item = (usize, T)>
where
    I: IntoIterator<Item = T>,
    T: Ord + Copy,
{
    let mut max = None;
    values
        .into_iter()
        .enumerate()
        .filter_map(move |(i, x)| match max {
            None => {
                max = Some(x);
                Some((i, x))
            }
            Some(m) if m < x => {
                max = Some(x);
                Some((i, x))
            }
            Some(_) => None,
        })
}

#[must_use]
fn left_visibility<T: Ord + Copy>(array: ArrayView2<T>) -> Array2<bool> {
    let mut visible = Array2::default(array.raw_dim());
    for (i, row) in array.rows().into_iter().enumerate() {
        for j in prefix_argmax(row.iter()).map(|(k, _)| k) {
            visible[[i, j]] = true;
        }
    }
    visible
}

#[must_use]
fn right_visibility<T: Ord + Copy>(array: ArrayView2<T>) -> Array2<bool> {
    let shape = array.shape();
    let mut visible = Array2::default(array.raw_dim());
    for (i, row) in array.rows().into_iter().enumerate() {
        for j in prefix_argmax(row.iter().rev()).map(|(k, _)| k) {
            visible[[i, shape[1] - 1 - j]] = true;
        }
    }
    visible
}

#[must_use]
fn top_visibility<T: Ord + Copy>(array: ArrayView2<T>) -> Array2<bool> {
    let mut visible = Array2::default(array.raw_dim());
    for (j, col) in array.columns().into_iter().enumerate() {
        for i in prefix_argmax(col.iter()).map(|(k, _)| k) {
            visible[[i, j]] = true;
        }
    }
    visible
}

#[must_use]
fn bottom_visibility<T: Ord + Copy>(array: ArrayView2<T>) -> Array2<bool> {
    let shape = array.shape();
    let mut visible = Array2::default(array.raw_dim());
    for (j, col) in array.columns().into_iter().enumerate() {
        for i in prefix_argmax(col.iter().rev()).map(|(k, _)| k) {
            visible[[shape[0] - 1 - i, j]] = true;
        }
    }
    visible
}

#[must_use]
pub fn visibility<T: Ord + Copy>(array: ArrayView2<T>) -> Array2<bool> {
    let left = left_visibility(array);
    let right = right_visibility(array);
    let top = top_visibility(array);
    let bottom = bottom_visibility(array);
    left | right | top | bottom
}

#[must_use]
pub fn solve_part1(array: ArrayView2<u8>) -> usize {
    visibility(array).iter().filter(|x| **x).count()
}

#[must_use]
fn left_viewing_distance<T: Ord + Copy>(array: ArrayView2<T>) -> Array2<usize> {
    let shape = array.shape();
    let nrows = shape[0];
    let ncols = shape[1];
    let visible = left_visibility(array.view());
    let mut distances = Array2::default(array.raw_dim());
    for i in 0..nrows {
        for j in 1..ncols {
            distances[[i, j]] = (0..j)
                .rev()
                .take_while(|&k| array[[i, j]] > array[[i, k]])
                .count();
            if !visible[[i, j]] {
                distances[[i, j]] += 1;
            }
        }
    }
    distances
}

#[must_use]
fn right_viewing_distance<T: Ord + Copy>(array: ArrayView2<T>) -> Array2<usize> {
    let shape = array.shape();
    let nrows = shape[0];
    let ncols = shape[1];
    let visible = right_visibility(array.view());
    let mut distances = Array2::default(array.raw_dim());
    for i in 0..nrows {
        for j in 0..ncols - 1 {
            distances[[i, j]] = (j + 1..ncols)
                .take_while(|&k| array[[i, j]] > array[[i, k]])
                .count();
            if !visible[[i, j]] {
                distances[[i, j]] += 1;
            }
        }
    }
    distances
}

#[must_use]
fn top_viewing_distance<T: Ord + Copy>(array: ArrayView2<T>) -> Array2<usize> {
    let shape = array.shape();
    let nrows = shape[0];
    let ncols = shape[1];
    let visible = top_visibility(array.view());
    let mut distances = Array2::default(array.raw_dim());
    for i in 1..nrows {
        for j in 0..ncols {
            distances[[i, j]] = (0..i)
                .rev()
                .take_while(|&k| array[[i, j]] > array[[k, j]])
                .count();
            if !visible[[i, j]] {
                distances[[i, j]] += 1;
            }
        }
    }
    distances
}

#[must_use]
fn bottom_viewing_distance<T: Ord + Copy>(array: ArrayView2<T>) -> Array2<usize> {
    let shape = array.shape();
    let nrows = shape[0];
    let ncols = shape[1];
    let visible = bottom_visibility(array.view());
    let mut distances = Array2::default(array.raw_dim());
    for i in 0..nrows - 1 {
        for j in 0..ncols {
            distances[[i, j]] = (i + 1..nrows)
                .take_while(|&k| array[[i, j]] > array[[k, j]])
                .count();
            if !visible[[i, j]] {
                distances[[i, j]] += 1;
            }
        }
    }
    distances
}

#[must_use]
pub fn scenic_score<T: Ord + Copy>(array: ArrayView2<T>) -> Array2<usize> {
    let left = left_viewing_distance(array);
    let right = right_viewing_distance(array);
    let top = top_viewing_distance(array);
    let bottom = bottom_viewing_distance(array);
    left * right * top * bottom
}

/// Finds the highest scenic score of any tree.
///
/// # Panics
///
/// Panics if the array is empty.
#[must_use]
pub fn solve_part2(array: ArrayView2<u8>) -> usize {
    scenic_score(array).iter().copied().max().unwrap()
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_prefix_argmax() {
        let xs = [0, 1, 3, 0, 2, 0, 1, 4, 2];
        let prefix_maxima: Vec<_> = prefix_argmax(xs).collect();
        let expected = [(0, 0), (1, 1), (2, 3), (7, 4)];
        assert_eq!(prefix_maxima, expected);
    }

    #[test]
    fn test_part1_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let array = parse_input(&input)?;
        let num_visible = solve_part1(array.view());
        assert_eq!(num_visible, 21);
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let array = parse_input(&input)?;
        let num_visible = solve_part1(array.view());
        assert_eq!(num_visible, 1812);
        Ok(())
    }

    #[test]
    fn test_part2_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let array = parse_input(&input)?;
        let score = solve_part2(array.view());
        assert_eq!(score, 8);
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let array = parse_input(&input)?;
        let score = solve_part2(array.view());
        assert_eq!(score, 315495);
        Ok(())
    }
}
