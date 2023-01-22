//! Solutions to [Advent of Code 2022 Day 23](https://adventofcode.com/2022/day/23).

use std::hash::Hash;
use std::io;
use std::ops::Add;

use ahash::{HashMap, HashMapExt, HashSet, HashSetExt};
use thiserror::Error;

/// The error type for operations in this crate.
#[derive(Debug, Error)]
pub enum Error {
    /// An underlying [`io::Error`].
    #[error("I/O error")]
    Io(#[from] io::Error),

    /// An error parsing the input.
    #[error("Parse error: invalid char: '{0}'")]
    Parse(char),
}

/// A specialized [`Result`] type for operations in this crate.
///
/// [`Result`]: std::result::Result
pub type Result<T> = std::result::Result<T, Error>;

/// The coordinates of an elf.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Position([isize; 2]);

impl Position {
    /// Creates a new position from row and column indices.
    #[must_use]
    pub fn new(i: isize, j: isize) -> Self {
        Self([i, j])
    }

    /// Returns an array of the row and column indices of this point.
    #[must_use]
    #[inline]
    pub fn to_array(&self) -> [isize; 2] {
        self.0
    }

    #[must_use]
    #[inline]
    pub fn row(&self) -> isize {
        self.0[0]
    }

    #[must_use]
    #[inline]
    pub fn column(&self) -> isize {
        self.0[1]
    }

    /// Returns an array of this point's neighboring points.
    #[must_use]
    #[inline]
    pub fn neighbors(&self) -> [Self; 8] {
        [
            *self + [-1, -1],
            *self + [-1, 0],
            *self + [-1, 1],
            *self + [0, -1],
            *self + [0, 1],
            *self + [1, -1],
            *self + [1, 0],
            *self + [1, 1],
        ]
    }

    /// Returns an array of this point's neighboring points in the given direction.
    #[must_use]
    #[inline]
    pub fn directed_neighbors(&self, direction: Direction) -> [Self; 3] {
        match direction {
            Direction::North => [*self + [-1, -1], *self + [-1, 0], *self + [-1, 1]],
            Direction::South => [*self + [1, -1], *self + [1, 0], *self + [1, 1]],
            Direction::West => [*self + [-1, -1], *self + [0, -1], *self + [1, -1]],
            Direction::East => [*self + [-1, 1], *self + [0, 1], *self + [1, 1]],
        }
    }

    #[must_use]
    #[inline]
    pub fn step(&self, direction: Direction) -> Self {
        let i = self.0[0];
        let j = self.0[1];
        match direction {
            Direction::North => [i - 1, j].into(),
            Direction::South => [i + 1, j].into(),
            Direction::West => [i, j - 1].into(),
            Direction::East => [i, j + 1].into(),
        }
    }
}

impl From<[isize; 2]> for Position {
    fn from(array: [isize; 2]) -> Self {
        Self(array)
    }
}

impl Add for Position {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self([self.row() + rhs.row(), self.column() + rhs.column()])
    }
}

impl Add<[isize; 2]> for Position {
    type Output = Self;

    fn add(self, rhs: [isize; 2]) -> Self {
        Self([self.row() + rhs[0], self.column() + rhs[1]])
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Direction {
    North = 0,
    South = 1,
    West = 2,
    East = 3,
}

#[derive(Debug, Clone)]
/// A set of elves on a two-dimensional coordinate grid.
pub struct Elves {
    pub positions: HashSet<Position>,
    direction_order: [Direction; 4],
}

impl Elves {
    #[must_use]
    pub fn new(positions: HashSet<Position>) -> Self {
        Self {
            positions,
            direction_order: [
                Direction::North,
                Direction::South,
                Direction::West,
                Direction::East,
            ],
        }
    }

    /// Returns `true` iff there is at least one elf in the cells that neighbor a given `position`.
    #[must_use]
    pub fn has_neighbors(&self, position: &Position) -> bool {
        position
            .neighbors()
            .iter()
            .any(|p| self.positions.contains(p))
    }

    /// Returns `true` iff there is at least one elf in the cells that neighbor a given `position`
    /// in the given `direction`.
    #[must_use]
    pub fn has_directed_neighbors(&self, position: &Position, direction: &Direction) -> bool {
        position
            .directed_neighbors(*direction)
            .iter()
            .any(|p| self.positions.contains(p))
    }

    /// Performs one round of elf shuffling and returns the number of elves that moved.
    #[must_use]
    pub fn do_round(&mut self) -> usize {
        let mut targets = Vec::new();
        for elf in &self.positions {
            let mut target = None;
            if self.has_neighbors(elf) {
                if let Some(&direction) = self
                    .direction_order
                    .iter()
                    .find(|direction| !self.has_directed_neighbors(elf, direction))
                {
                    target = Some(elf.step(direction));
                }
            }
            targets.push((*elf, target));
        }

        // Count how many times each new position was proposed.
        let mut counts = HashMap::new();
        for (_, target) in &targets {
            if let Some(p) = target {
                *counts.entry(*p).or_insert(0) += 1;
            }
        }
        let num_moved = counts.values().filter(|&&count| count == 1).count();

        let new_positions = targets
            .into_iter()
            .map(|(current, proposed)| {
                let mut pos = current;
                if let Some(p) = proposed {
                    if counts.get(&p) == Some(&1) {
                        pos = p;
                    }
                }
                pos
            })
            .collect();
        self.positions = new_positions;
        self.direction_order.rotate_left(1);
        num_moved
    }

    #[must_use]
    pub fn bounding_box(&self) -> [[Option<isize>; 2]; 2] {
        let row_min = self.positions.iter().map(Position::row).min();
        let row_max = self.positions.iter().map(Position::row).max();
        let col_min = self.positions.iter().map(Position::column).min();
        let col_max = self.positions.iter().map(Position::column).max();
        [[row_min, row_max], [col_min, col_max]]
    }

    #[must_use]
    pub fn count_empty_tiles(&self) -> Option<usize> {
        let num_elves = self.positions.len();
        let bounding_box = self.bounding_box();
        let row_min = bounding_box[0][0]?;
        let row_max = bounding_box[0][1]?;
        let col_min = bounding_box[1][0]?;
        let col_max = bounding_box[1][1]?;
        let area = (row_max - row_min + 1).unsigned_abs() * (col_max - col_min + 1).unsigned_abs();
        Some(area - num_elves)
    }
}

pub fn solve_part1(elves: &mut Elves) -> usize {
    for _ in 0..10 {
        let _ = elves.do_round();
    }
    elves.count_empty_tiles().expect("there are elves")
}

pub fn solve_part2(elves: &mut Elves) -> usize {
    let mut round = 1;
    while elves.do_round() > 0 {
        round += 1;
    }
    round
}

/// Parses the input into a set of elves placed on a two-dimensional coordinate grid.
///
/// # Errors
///
/// Returns an error if there is a character other than `'.'` or `'#'` on any line of the input.
pub fn parse_input(s: &str) -> Result<Elves> {
    let mut positions = HashSet::new();
    for (i, line) in s.lines().enumerate() {
        let row = parse_row(i, line)?;
        positions.extend(row);
    }
    Ok(Elves::new(positions))
}

/// Returns the positions of the elves on row `i` of the input.
fn parse_row(i: usize, s: &str) -> Result<Vec<Position>> {
    s.chars()
        .enumerate()
        .filter_map(|(j, c)| match c {
            '.' => None,
            '#' => Some(Ok(Position::new(i as isize, j as isize))),
            _ => Some(Err(Error::Parse(c))),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_part1_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let mut elves = parse_input(&input)?;
        let num_empty = solve_part1(&mut elves);
        assert_eq!(num_empty, 110);
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let mut elves = parse_input(&input)?;
        let num_empty = solve_part1(&mut elves);
        assert_eq!(num_empty, 4005);
        Ok(())
    }

    #[test]
    fn test_part2_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let mut elves = parse_input(&input)?;
        let num_empty = solve_part2(&mut elves);
        assert_eq!(num_empty, 20);
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let mut elves = parse_input(&input)?;
        let num_empty = solve_part2(&mut elves);
        assert_eq!(num_empty, 1008);
        Ok(())
    }
}
