//! Solutions to [Advent of Code 2022 Day 14](https://adventofcode.com/2022/day/14).

use std::io;

pub use ndarray::Array2;
use thiserror::Error;

/// The error type for operations in this crate.
#[derive(Debug, Error)]
pub enum Error {
    /// An underlying [`io::Error`].
    #[error("I/O error")]
    Io(#[from] io::Error),

    /// An error parsing input
    #[error("Parse error")]
    Parse,

    /// Invalid path segment
    #[error("Invalid path segment")]
    InvalidSegment(Point<usize>, Point<usize>),
}

/// A specialized [`Result`] type for operations in this crate.
///
/// [`Result`]: std::result::Result
pub type Result<T> = std::result::Result<T, Error>;

pub type Point<T> = (T, T);

pub fn parse_input(s: &str) -> Result<Vec<Vec<Point<usize>>>> {
    let (_, paths) = parser::parse_input_inner(s).map_err(|_| Error::Parse)?;
    Ok(paths)
}

pub use part1::solve_part1;

pub mod part1 {
    use std::cmp::{max, min};

    use ndarray::Array2;

    use crate::{Error, Point, Result};

    fn build_array(paths: &[Vec<Point<usize>>]) -> Result<Array2<bool>> {
        let maxx = paths
            .iter()
            .flat_map(|line| line.iter().map(|&(x, _)| x))
            .max()
            .unwrap_or(0);
        let maxy = paths
            .iter()
            .flat_map(|line| line.iter().map(|&(_, y)| y))
            .max()
            .unwrap_or(0);
        let mut occupied: Array2<bool> = Array2::default((maxx + 2, maxy + 1));
        for path in paths {
            for coordinates in path.windows(2) {
                let (x0, y0) = coordinates[0];
                let (x1, y1) = coordinates[1];
                if x0 == x1 {
                    (min(y0, y1)..=max(y0, y1)).for_each(|y| occupied[[x0, y]] = true);
                } else if y0 == y1 {
                    (min(x0, x1)..=max(x0, x1)).for_each(|x| occupied[[x, y0]] = true);
                } else {
                    return Err(Error::InvalidSegment((x0, y0), (x1, y1)));
                }
            }
        }
        Ok(occupied)
    }

    /// Adds a grain of sand to the grid and returns `true` if it comes to rest and `false` otherwise.
    fn drop_sand(occupied: &mut Array2<bool>, point: Point<usize>) -> bool {
        let ncols = occupied.shape()[1];
        let (x0, y0) = point;
        if let Some(y) = (y0..ncols).find(|&y| occupied[[x0, y]]) {
            if !occupied[[x0 - 1, y]] {
                drop_sand(occupied, (x0 - 1, y))
            } else if !occupied[[x0 + 1, y]] {
                drop_sand(occupied, (x0 + 1, y))
            } else {
                occupied[[x0, y - 1]] = true;
                true
            }
        } else {
            false
        }
    }

    pub fn solve_part1(paths: &[Vec<Point<usize>>]) -> Result<usize> {
        let mut occupied = build_array(paths)?;
        let mut count = 0;
        while drop_sand(&mut occupied, (500, 0)) {
            count += 1;
        }
        Ok(count)
    }
}

pub use part2::solve_part2;

pub mod part2 {
    use std::cmp::{max, min};

    use ndarray::Array2;

    use crate::{Error, Point, Result};

    fn build_array(paths: &[Vec<Point<usize>>]) -> Result<Array2<bool>> {
        let maxx = paths
            .iter()
            .flat_map(|line| line.iter().map(|&(x, _)| x))
            .max()
            .unwrap_or(0);
        let maxy = paths
            .iter()
            .flat_map(|line| line.iter().map(|&(_, y)| y))
            .max()
            .unwrap_or(0);
        let mut occupied: Array2<bool> = Array2::default((maxx + maxy + 1, maxy + 3));
        for path in paths {
            for coordinates in path.windows(2) {
                let (x0, y0) = coordinates[0];
                let (x1, y1) = coordinates[1];
                if x0 == x1 {
                    (min(y0, y1)..=max(y0, y1)).for_each(|y| occupied[[x0, y]] = true);
                } else if y0 == y1 {
                    (min(x0, x1)..=max(x0, x1)).for_each(|x| occupied[[x, y0]] = true);
                } else {
                    return Err(Error::InvalidSegment((x0, y0), (x1, y1)));
                }
            }
        }
        (0..maxx + maxy + 1).for_each(|x| occupied[[x, maxy + 2]] = true);
        Ok(occupied)
    }

    /// Attempts to add a grain of sand and returns `true` if this is possible.
    fn drop_sand(occupied: &mut Array2<bool>, point: Point<usize>) -> bool {
        let ncols = occupied.shape()[1];
        let (x0, y0) = point;
        let y = (y0..ncols)
            .find(|&y| occupied[[x0, y]])
            .expect("there is a solid floor");
        if y == 0 {
            false
        } else if !occupied[[x0 - 1, y]] {
            drop_sand(occupied, (x0 - 1, y))
        } else if !occupied[[x0 + 1, y]] {
            drop_sand(occupied, (x0 + 1, y))
        } else {
            occupied[[x0, y - 1]] = true;
            true
        }
    }

    pub fn solve_part2(paths: &[Vec<Point<usize>>]) -> Result<usize> {
        let mut occupied = build_array(paths)?;
        let mut count = 0;
        while drop_sand(&mut occupied, (500, 0)) {
            count += 1;
        }
        Ok(count)
    }
}
mod parser {
    use nom::{
        bytes::complete::tag,
        character::complete::{char, digit1, newline, space0},
        combinator::{all_consuming, map_res},
        multi::{many0, separated_list0},
        sequence::{delimited, separated_pair, terminated},
        IResult,
    };

    use crate::Point;

    pub(crate) fn parse_input_inner(s: &str) -> IResult<&str, Vec<Vec<Point<usize>>>> {
        all_consuming(many0(parse_path))(s)
    }

    fn parse_path(s: &str) -> IResult<&str, Vec<Point<usize>>> {
        terminated(separated_list0(parse_arrow, parse_point), newline)(s)
    }

    fn parse_arrow(s: &str) -> IResult<&str, &str> {
        delimited(space0, tag("->"), space0)(s)
    }

    fn parse_point(s: &str) -> IResult<&str, Point<usize>> {
        separated_pair(parse_integer, char(','), parse_integer)(s)
    }

    fn parse_integer(s: &str) -> IResult<&str, usize> {
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
        let paths = parse_input(&input)?;
        let count = solve_part1(&paths)?;
        assert_eq!(count, 24);
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let paths = parse_input(&input)?;
        let count = solve_part1(&paths)?;
        assert_eq!(count, 979);
        Ok(())
    }

    #[test]
    fn test_part2_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let paths = parse_input(&input)?;
        let count = solve_part2(&paths)?;
        assert_eq!(count, 93);
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let paths = parse_input(&input)?;
        let count = solve_part2(&paths)?;
        assert_eq!(count, 29044);
        Ok(())
    }
}
