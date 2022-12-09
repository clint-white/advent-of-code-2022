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

#[derive(Debug, Default, Copy, Clone)]
pub struct Rope {
    head: Position<i32>,
    tail: Position<i32>,
}

impl Rope {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn head(&self) -> Position<i32> {
        self.head
    }

    pub fn tail(&self) -> Position<i32> {
        self.tail
    }

    /// Move the rope by moving the head in the given direction.
    pub fn move_head(&mut self, direction: Direction) {
        let delta: Position<i32> = direction.into();
        self.head += delta;
        self.adjust_tail();
    }

    fn adjust_tail(&mut self) {
        let delta = self.head - self.tail;
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
            _ => unreachable!(),
        };
        self.tail += Position::new(dx, dy);
    }
}

pub fn solve_part1(motions: &[Motion]) -> usize {
    let mut tail_positions = HashMap::new();
    let mut rope = Rope::new();
    *tail_positions.entry(rope.tail()).or_insert(0) += 1;
    for motion in motions {
        for _ in 0..motion.distance {
            rope.move_head(motion.direction);
            *tail_positions.entry(rope.tail()).or_insert(0) += 1;
        }
    }
    tail_positions.len()
}

/// Parses an input `str` into a vector of [`Motion`] commands.
///
/// # Errors
///
/// This function returns an error if it cannot parse the input.
pub fn parse_input(s: &str) -> Result<Vec<Motion>> {
    s.lines().map(|line| line.parse()).collect()
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
        todo!();
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        todo!();
    }
}
