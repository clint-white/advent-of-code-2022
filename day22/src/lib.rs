//! Solutions to [Advent of Code 2022 Day 22](https://adventofcode.com/2022/day/22).

use std::hash::Hash;
use std::io;
use std::num::ParseIntError;
use std::str::FromStr;

use once_cell::sync::OnceCell;
use regex::Regex;
use thiserror::Error;

pub mod grid;
pub use grid::Grid;
pub mod part1;
pub mod part2;

macro_rules! regex {
    ($re:literal $(,)?) => {{
        static RE: OnceCell<Regex> = OnceCell::new();
        RE.get_or_init(|| Regex::new($re).unwrap())
    }};
}

/// The error type for operations in this crate.
#[derive(Debug, Error)]
pub enum Error {
    /// An underlying [`io::Error`].
    #[error("I/O error")]
    Io(#[from] io::Error),

    /// Input did not contain a blank line between grid and instructions.
    #[error("Parse error: missing blank line")]
    MissingBlankLine,

    /// An error parsing a rotation.
    #[error("Not a valid rotation: '{0}'")]
    ParseRotation(String),

    /// An error parsing an integer.
    #[error("Error parsing integer")]
    ParseInt(#[from] ParseIntError),

    /// An error parsing the map.
    #[error("Invalid map cell character: '{0}'")]
    ParseMap(char),

    /// An error with the shape of the grid.
    #[error("An error with the shape of the grid")]
    Grid(#[from] grid::Error),

    /// No open tile on the first row of the board.
    #[error("No open tile on the first row of the board")]
    MissingSource,
}

/// A specialized [`Result`] type for operations in this crate.
///
/// [`Result`]: std::result::Result
pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Heading {
    /// East
    Right = 0,
    /// South
    Down = 1,
    /// West
    Left = 2,
    /// North
    Up = 3,
}

impl Heading {
    /// Updates the heading after rotating in the given direction.
    pub fn rotate(&mut self, direction: Rotation) {
        use Heading::{Down, Left, Right, Up};
        use Rotation::{Clockwise, CounterClockwise};

        *self = match (&self, direction) {
            (&Right, Clockwise) | (&Left, CounterClockwise) => Down,
            (&Right, CounterClockwise) | (&Left, Clockwise) => Up,
            (&Down, Clockwise) | (&Up, CounterClockwise) => Left,
            (&Down, CounterClockwise) | (&Up, Clockwise) => Right,
        };
    }

    #[must_use]
    pub fn facing(&self) -> usize {
        *self as usize
    }

    pub fn reverse(&self) -> Self {
        use Heading::{Down, Left, Right, Up};

        match self {
            Down => Up,
            Up => Down,
            Right => Left,
            Left => Right,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Rotation {
    Clockwise,
    CounterClockwise,
}

impl FromStr for Rotation {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        match s {
            "R" => Ok(Self::Clockwise),
            "L" => Ok(Self::CounterClockwise),
            _ => Err(Error::ParseRotation(s.into())),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Instruction {
    Forward(usize),
    Rotate(Rotation),
}

/// Row and column indices relative to the square grid.
pub type Position = [usize; 2];

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum CellKind {
    OpenTile,
    SolidWall,
}

/// Parses the input into a grid of cells and an vector of instructions.
///
/// # Errors
///
/// Returns an error if the input does not contain both a grid and a set of instructions.  Also
/// returns an error if the grid or the instructions cannot be parsed properly.
pub fn parse_input(s: &str) -> Result<(Grid<Option<CellKind>>, Vec<Instruction>)> {
    let (part1, part2) = s.split_once("\n\n").ok_or(Error::MissingBlankLine)?;
    let map = parse_map(part1)?;
    let instructions = parse_instructions(part2)?;
    Ok((map, instructions))
}

fn parse_map(s: &str) -> Result<Grid<Option<CellKind>>> {
    // Add in a border of void cells.  This makes it easier to work with edge cases and it also
    // gets the 1-up indexing of rows and columns for the grid proper that the problem uses.
    let num_cols = s.lines().map(str::len).max().unwrap_or(0) + 2;

    let mut grid = Grid::new(num_cols);
    grid.push_row(vec![None; num_cols])?;

    for line in s.lines() {
        let mut row = vec![None; num_cols];
        for (cell, c) in row[1..num_cols - 1].iter_mut().zip(line.chars()) {
            let kind = match c {
                '.' => Some(CellKind::OpenTile),
                '#' => Some(CellKind::SolidWall),
                ' ' => None,
                _ => {
                    return Err(Error::ParseMap(c));
                }
            };
            *cell = kind;
        }
        grid.push_row(row)?;
    }
    grid.push_row(vec![None; num_cols])?;
    Ok(grid)
}

fn parse_instructions(s: &str) -> Result<Vec<Instruction>> {
    let re = regex!(r"(?P<num>[[:digit:]]+)|(?P<dir>L|R)");
    let mut instructions = Vec::new();
    for caps in re.captures_iter(s) {
        let instr = if let Some(num) = caps.name("num") {
            Instruction::Forward(num.as_str().parse()?)
        } else {
            // If the `num` group does not match, then it must be that the `dir` group does.
            Instruction::Rotate(caps["dir"].parse()?)
        };
        instructions.push(instr);
    }
    Ok(instructions)
}
