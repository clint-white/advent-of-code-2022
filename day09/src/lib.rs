//! Solutions to [Advent of Code 2022 Day 9](https://adventofcode.com/2022/day/9).

use std::collections::HashMap;
use std::io;
use std::num::ParseIntError;
use std::ops::{Add, AddAssign, Sub, SubAssign};
use std::str::FromStr;

use thiserror::Error;

/// The error type for operations in this crate.
#[derive(Debug, Error)]
pub enum Error {
    /// An underlying [`io::Error`].
    #[error("I/O error")]
    Io(#[from] io::Error),

    /// An error parsing a [`Direction`].
    #[error("Error parsing direction: '{0}'")]
    ParseDirection(String),

    /// An error parsing a [`Motion`].
    #[error("Error parsing motion: '{0}'")]
    ParseMotion(String),

    /// An error parsing an int.
    #[error("Error parsing integer")]
    ParseInt(#[from] ParseIntError),
}

/// A specialized [`Result`] type for operations in this crate.
///
/// [`Result`]: std::result::Result
pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Direction {
    Up,
    Down,
    Left,
    Right,
}

impl FromStr for Direction {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        match s {
            "U" => Ok(Self::Up),
            "D" => Ok(Self::Down),
            "L" => Ok(Self::Left),
            "R" => Ok(Self::Right),
            _ => Err(Error::ParseDirection(s.into())),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Motion {
    pub direction: Direction,
    pub distance: u16,
}

impl FromStr for Motion {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        let (dir, steps) = s
            .split_once(' ')
            .ok_or_else(|| Error::ParseMotion(s.into()))?;
        let direction = dir.parse()?;
        let distance = steps.parse()?;
        let motion = Motion {
            direction,
            distance,
        };
        Ok(motion)
    }
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Position<T> {
    pub x: T,
    pub y: T,
}

impl<T> Position<T> {
    pub fn new(x: T, y: T) -> Self {
        Self { x, y }
    }
}

impl<T: Add<Output = T>> Add for Position<T> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self {
            x: self.x + other.x,
            y: self.y + other.y,
        }
    }
}

impl<T: AddAssign> AddAssign for Position<T> {
    fn add_assign(&mut self, other: Self) {
        self.x += other.x;
        self.y += other.y;
    }
}

impl<T: Sub<Output = T>> Sub for Position<T> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        Self {
            x: self.x - other.x,
            y: self.y - other.y,
        }
    }
}

impl<T: SubAssign> SubAssign for Position<T> {
    fn sub_assign(&mut self, other: Self) {
        self.x -= other.x;
        self.y -= other.y;
    }
}

impl Add<Direction> for Position<i32> {
    type Output = Self;

    fn add(self, rhs: Direction) -> Self {
        let other: Self = rhs.into();
        self + other
    }
}

impl From<Direction> for Position<i32> {
    fn from(direction: Direction) -> Self {
        let (x, y) = match direction {
            Direction::Up => (0, 1),
            Direction::Down => (0, -1),
            Direction::Left => (-1, 0),
            Direction::Right => (1, 0),
        };
        Self { x, y }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Rope<const N: usize> {
    knots: [Position<i32>; N],
}

impl<const N: usize> Default for Rope<N> {
    fn default() -> Self {
        Self {
            knots: [Position::default(); N],
        }
    }
}

impl<const N: usize> Rope<N> {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the position of knot `i`.
    ///
    /// # Panics
    ///
    /// Panics if `i >= N`.
    #[must_use]
    #[inline]
    pub fn knot(&self, i: usize) -> Position<i32> {
        self.knots[i]
    }

    /// Returns the position of the tail knot.
    #[must_use]
    #[inline]
    pub fn tail(&self) -> Position<i32> {
        self.knot(N - 1)
    }

    /// Move the rope by moving the head in the given direction.
    pub fn move_head(&mut self, direction: Direction) {
        let delta: Position<i32> = direction.into();
        self.knots[0] += delta;
        for i in 0..N - 1 {
            self.adjust_next_knot(i);
        }
    }

    /// Adjust the position of knot `i + 1` to follow knot `i`.
    fn adjust_next_knot(&mut self, i: usize) {
        let delta = self.knots[i] - self.knots[i + 1];
        if N == 2 {
            assert!(delta.x.abs() < 2 || delta.y.abs() < 2);
        }
        let (dx, dy) = match (delta.x, delta.y) {
            (0, 2) => (0, 1),
            (0, -2) => (0, -1),
            (2, 0) => (1, 0),
            (-2, 0) => (-1, 0),
            (1, 0)
            | (-1, 0)
            | (0, 1)
            | (0, -1)
            | (1, -1)
            | (-1, 1)
            | (1, 1)
            | (-1, -1)
            | (0, 0) => (0, 0),
            (1, 2) | (2, 1) => (1, 1),
            (1, -2) | (2, -1) => (1, -1),
            (-1, 2) | (-2, 1) => (-1, 1),
            (-1, -2) | (-2, -1) => (-1, -1),
            // the following cases are unreachable for `N == 2`
            (2, 2) => (1, 1),
            (2, -2) => (1, -1),
            (-2, 2) => (-1, 1),
            (-2, -2) => (-1, -1),
            _ => unreachable!(),
        };
        self.knots[i + 1] += Position::new(dx, dy);
    }
}

#[must_use]
pub fn count_unique_tail_positions<const N: usize>(motions: &[Motion]) -> usize {
    let mut tail_positions = HashMap::new();
    let mut rope = Rope::<N>::new();
    *tail_positions.entry(rope.tail()).or_insert(0) += 1;
    for motion in motions {
        for _ in 0..motion.distance {
            rope.move_head(motion.direction);
            *tail_positions.entry(rope.tail()).or_insert(0) += 1;
        }
    }
    tail_positions.len()
}

#[must_use]
pub fn solve_part1(motions: &[Motion]) -> usize {
    count_unique_tail_positions::<2>(motions)
}

#[must_use]
pub fn solve_part2(motions: &[Motion]) -> usize {
    count_unique_tail_positions::<10>(motions)
}

/// Parses an input `str` into a vector of [`Motion`] commands.
///
/// # Errors
///
/// This function returns an error if it cannot parse the input.
pub fn parse_input(s: &str) -> Result<Vec<Motion>> {
    s.lines().map(str::parse).collect()
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_part1_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let motions = parse_input(&input)?;
        let num_positions = solve_part1(&motions);
        assert_eq!(num_positions, 13);
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let motions = parse_input(&input)?;
        let num_positions = solve_part1(&motions);
        assert_eq!(num_positions, 5735);
        Ok(())
    }

    #[test]
    fn test_part2_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let motions = parse_input(&input)?;
        let num_positions = solve_part2(&motions);
        assert_eq!(num_positions, 1);
        Ok(())
    }

    #[test]
    fn test_part2_example2() -> Result<()> {
        let input = fs::read_to_string("data/example2")?;
        let motions = parse_input(&input)?;
        let num_positions = solve_part2(&motions);
        assert_eq!(num_positions, 36);
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let motions = parse_input(&input)?;
        let num_positions = solve_part2(&motions);
        assert_eq!(num_positions, 2478);
        Ok(())
    }
}
