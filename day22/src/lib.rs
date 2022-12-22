//! Solutions to [Advent of Code 2022 Day 22](https://adventofcode.com/2022/day/22).

use std::collections::HashMap;
use std::hash::Hash;
use std::io;
use std::num::ParseIntError;
use std::ops::{Index, IndexMut};
use std::str::FromStr;

use once_cell::sync::OnceCell;
use regex::Regex;
use thiserror::Error;

pub mod grid;
pub use grid::Grid;

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

/// An array of the positions of a cell's neighbors in each of four directions.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Neighbors([Option<Position>; 4]);

impl Index<Heading> for Neighbors {
    type Output = Option<Position>;

    fn index(&self, heading: Heading) -> &Self::Output {
        self.0.index(heading as usize)
    }
}

impl IndexMut<Heading> for Neighbors {
    fn index_mut(&mut self, heading: Heading) -> &mut Self::Output {
        self.0.index_mut(heading as usize)
    }
}

/// The position and heading on the board.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct State {
    pub position: Position,
    pub heading: Heading,
}

impl State {
    #[must_use]
    pub fn password(&self) -> usize {
        1000 * self.position[0] + 4 * self.position[1] + self.heading.facing()
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum CellKind {
    OpenTile,
    SolidWall,
}

#[derive(Debug, Clone)]
pub struct Graph {
    edges: HashMap<Position, Neighbors>,
    source: State,
}

impl Graph {
    /// Returns the position of the neighbor of a given postion in the given direction.
    #[must_use]
    pub fn neighbor(&self, position: Position, heading: Heading) -> Option<Position> {
        self.edges[&position][heading]
    }

    #[must_use]
    pub fn source(&self) -> State {
        self.source
    }
}

#[must_use]
pub fn solve_part1(graph: &Graph, instructions: &[Instruction]) -> usize {
    let mut state = graph.source();
    for &instruction in instructions {
        match instruction {
            Instruction::Forward(steps) => {
                for _ in 0..steps {
                    if let Some(pos) = graph.neighbor(state.position, state.heading) {
                        state.position = pos;
                    } else {
                        break;
                    }
                }
            }
            Instruction::Rotate(dir) => {
                state.heading.rotate(dir);
            }
        }
    }
    state.password()
}

/// Builds a graph from a grid of cells.
///
/// # Errors
///
/// Returns an error if the implicit source of the graph, i.e., the first open tile on the first
/// row, does not exist.
pub fn build_graph(grid: &Grid<Option<CellKind>>) -> Result<Graph> {
    use CellKind::OpenTile;
    use Heading::{Down, Left, Right, Up};

    // Initialize the graph so that the nodes are the open tiles in the grid and each node has no
    // neighbors at this point.
    let mut edges = HashMap::new();
    for i in 1..grid.num_rows() - 1 {
        for j in 1..grid.num_cols() - 1 {
            let pos = [i, j];
            if let Some(CellKind::OpenTile) = grid[pos] {
                edges.insert(pos, Neighbors::default());
            }
        }
    }

    // Add right and left neighbors.
    for i in 1..grid.num_rows() - 1 {
        // Right neighbors
        // Track the cell an entry in this row would wrap around to.
        let mut wrap_around = None;
        for j in 1..grid.num_cols() - 1 {
            if matches!((grid[[i, j - 1]], grid[[i, j]]), (None, Some(OpenTile))) {
                wrap_around = Some([i, j]);
            }
            match (grid[[i, j]], grid[[i, j + 1]]) {
                (Some(OpenTile), Some(OpenTile)) => {
                    let neighbors = edges.get_mut(&[i, j]).expect("open tiles are in the edges");
                    neighbors[Right] = Some([i, j + 1]);
                }
                (Some(OpenTile), None) => {
                    let neighbors = edges.get_mut(&[i, j]).expect("open tiles are in the edges");
                    neighbors[Right] = wrap_around;
                }
                _ => (),
            }
        }

        // Left neighbors
        let mut wrap_around = None;
        for j in (1..grid.num_cols() - 1).rev() {
            if matches!((grid[[i, j + 1]], grid[[i, j]]), (None, Some(OpenTile))) {
                wrap_around = Some([i, j]);
            }
            match (grid[[i, j]], grid[[i, j - 1]]) {
                (Some(OpenTile), Some(OpenTile)) => {
                    let neighbors = edges.get_mut(&[i, j]).expect("open tiles are in the edges");
                    neighbors[Left] = Some([i, j - 1]);
                }
                (Some(OpenTile), None) => {
                    let neighbors = edges.get_mut(&[i, j]).expect("open tiles are in the edges");
                    neighbors[Left] = wrap_around;
                }
                _ => (),
            }
        }
    }

    // Add down and up neighbors.
    for j in 1..grid.num_cols() - 1 {
        // Down neighbors
        // Track the cell an entry in this row would wrap around to.
        let mut wrap_around = None;
        for i in 1..grid.num_rows() - 1 {
            if matches!((grid[[i - 1, j]], grid[[i, j]]), (None, Some(OpenTile))) {
                wrap_around = Some([i, j]);
            }
            match (grid[[i, j]], grid[[i + 1, j]]) {
                (Some(OpenTile), Some(OpenTile)) => {
                    let neighbors = edges.get_mut(&[i, j]).expect("open tiles are in the edges");
                    neighbors[Down] = Some([i + 1, j]);
                }
                (Some(OpenTile), None) => {
                    let neighbors = edges.get_mut(&[i, j]).expect("open tiles are in the edges");
                    neighbors[Down] = wrap_around;
                }
                _ => (),
            }
        }

        // Up neighbors
        let mut wrap_around = None;
        for i in (1..grid.num_rows() - 1).rev() {
            if matches!((grid[[i + 1, j]], grid[[i, j]]), (None, Some(OpenTile))) {
                wrap_around = Some([i, j]);
            }
            match (grid[[i, j]], grid[[i - 1, j]]) {
                (Some(OpenTile), Some(OpenTile)) => {
                    let neighbors = edges.get_mut(&[i, j]).expect("open tiles are in the edges");
                    neighbors[Up] = Some([i - 1, j]);
                }
                (Some(OpenTile), None) => {
                    let neighbors = edges.get_mut(&[i, j]).expect("open tiles are in the edges");
                    neighbors[Up] = wrap_around;
                }
                _ => (),
            }
        }
    }
    let start_col = (1..grid.num_cols() - 1)
        .find(|&j| matches!(grid[[1, j]], Some(OpenTile)))
        .ok_or(Error::MissingSource)?;
    let source = State {
        position: [1, start_col],
        heading: Right,
    };

    let graph = Graph { edges, source };
    Ok(graph)
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

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_part1_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let (grid, instructions) = parse_input(&input)?;
        let graph = build_graph(&grid)?;
        let password = solve_part1(&graph, &instructions);
        assert_eq!(password, 6032);
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let (grid, instructions) = parse_input(&input)?;
        let graph = build_graph(&grid)?;
        let password = solve_part1(&graph, &instructions);
        assert_eq!(password, 55244);
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
