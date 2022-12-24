//! Solutions to [Advent of Code 2022 Day 24](https://adventofcode.com/2022/day/24).

use std::fmt;
use std::io;

use bitflags::bitflags;
use thiserror::Error;

use utils::Grid;

/// The error type for operations in this crate.
#[derive(Debug, Error)]
pub enum Error {
    /// An underlying [`io::Error`].
    #[error("I/O error")]
    Io(#[from] io::Error),

    /// Invalid shape of grid.
    #[error("Invalid shape of grid")]
    Shape(#[from] utils::Error),

    /// An invalid input character.
    #[error("Parse error: invalid char: '{0}'")]
    Parse(char),

    /// An invalid position (e.g., start or end cell is a wall).
    #[error("Invalid position: [{0}, {1}]: found {2}")]
    InvalidPosition(usize, usize, Blizzard),

    /// No solution was found after evolving for a limited number of steps.
    #[error("No solution found")]
    NoSolution,
}

/// A specialized [`Result`] type for operations in this crate.
///
/// [`Result`]: std::result::Result
pub type Result<T> = std::result::Result<T, Error>;

bitflags! {
    pub struct Blizzard: u8 {
        const UP = 0b0000_0001;
        const DOWN = 0b0000_0010;
        const LEFT = 0b0000_0100;
        const RIGHT = 0b0000_1000;
        const WALL = 0b1000_0000;
    }
}

impl TryFrom<char> for Blizzard {
    type Error = Error;

    fn try_from(c: char) -> Result<Self> {
        match c {
            '^' => Ok(Blizzard::UP),
            'v' => Ok(Blizzard::DOWN),
            '<' => Ok(Blizzard::LEFT),
            '>' => Ok(Blizzard::RIGHT),
            '#' => Ok(Blizzard::WALL),
            '.' => Ok(Blizzard::empty()),
            _ => Err(Error::Parse(c)),
        }
    }
}

impl fmt::Display for Blizzard {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let num = self.bits().count_ones();
        if num == 0 {
            write!(f, ".")
        } else if num == 1 {
            let c = match *self {
                Self::UP => '^',
                Self::DOWN => 'v',
                Self::LEFT => '<',
                Self::RIGHT => '>',
                Self::WALL => '#',
                _ => unreachable!(),
            };
            write!(f, "{c}")
        } else {
            write!(f, "{num}")
        }
    }
}

/// Returns the number of steps (including waits) in the optimal path from `start` to `end`
/// avoiding blizzards.
///
/// # Errors
///
/// Returns an error if either of the `start` or `end` positions are invalid, that is, if the
/// `start` position is not empty or if the `end` position is a wall.
pub fn chart_course(
    blizzards: &mut Grid<Blizzard>,
    start: [usize; 2],
    end: [usize; 2],
) -> Result<usize> {
    let mut possible: Grid<bool> = Grid::from_shape_default(blizzards.shape());
    if !blizzards[start].is_empty() {
        return Err(Error::InvalidPosition(start[0], start[1], blizzards[start]));
    }
    if blizzards[end].contains(Blizzard::WALL) {
        return Err(Error::InvalidPosition(end[0], end[1], blizzards[end]));
    }
    possible[start] = true;
    for t in 1.. {
        evolve(blizzards);
        possible = possible_positions(&possible, blizzards);
        if possible[end] {
            return Ok(t);
        }
    }
    Err(Error::NoSolution)
}

fn possible_positions(previous: &Grid<bool>, blizzards: &mut Grid<Blizzard>) -> Grid<bool> {
    let mut next = Grid::from_shape_default(previous.shape());
    let num_rows = next.num_rows();
    let num_cols = next.num_cols();

    // Update the interior.
    for i in 1..num_rows - 1 {
        for j in 1..num_cols - 1 {
            next[[i, j]] = blizzards[[i, j]].is_empty()
                && (previous[[i, j]]
                    || previous[[i - 1, j]]
                    || previous[[i + 1, j]]
                    || previous[[i, j - 1]]
                    || previous[[i, j + 1]]);
        }
    }

    // Now update the boundary.  First the edges minus the corners.
    for j in 1..num_cols - 1 {
        next[[0, j]] = blizzards[[0, j]].is_empty()
            && (previous[[0, j]]
                || previous[[1, j]]
                || previous[[0, j - 1]]
                || previous[[0, j + 1]]);
        next[[num_rows - 1, j]] = blizzards[[num_rows - 1, j]].is_empty()
            && (previous[[num_rows - 1, j]]
                || previous[[num_rows - 2, j]]
                || previous[[num_rows - 1, j - 1]]
                || previous[[num_rows - 1, j + 1]]);
    }
    for i in 1..num_rows - 1 {
        next[[i, 0]] = blizzards[[i, 0]].is_empty()
            && (previous[[i, 0]]
                || previous[[i - 1, 0]]
                || previous[[i + 1, 0]]
                || previous[[i, 1]]);
        next[[i, num_cols - 1]] = blizzards[[i, num_cols - 1]].is_empty()
            && (previous[[i, num_cols - 1]]
                || previous[[i, num_cols - 2]]
                || previous[[i - 1, num_cols - 1]]
                || previous[[i + 1, num_cols - 1]]);
    }

    // Now the corners.
    next[[0, 0]] =
        blizzards[[0, 0]].is_empty() && (previous[[0, 0]] || previous[[1, 0]] || previous[[0, 1]]);
    next[[0, num_cols - 1]] = blizzards[[0, num_cols - 1]].is_empty()
        && (previous[[0, num_cols - 1]]
            || previous[[1, num_cols - 1]]
            || previous[[0, num_cols - 2]]);
    next[[num_rows - 1, 0]] = blizzards[[num_rows - 1, 0]].is_empty()
        && (previous[[num_rows - 1, 0]]
            || previous[[num_rows - 2, 0]]
            || previous[[num_rows - 1, 1]]);
    next[[num_rows - 1, num_cols - 1]] = blizzards[[num_rows - 1, num_cols - 1]].is_empty()
        && (previous[[num_rows - 1, num_cols - 1]]
            || previous[[num_rows - 2, num_cols - 1]]
            || previous[[num_rows - 1, num_cols - 2]]);
    next
}

pub fn solve_part1(blizzards: &mut Grid<Blizzard>) -> usize {
    let start = blizzards
        .row(0)
        .enumerate()
        .find_map(|(j, cell)| if cell.is_empty() { Some([0, j]) } else { None })
        .expect("start position on first row");
    let n = blizzards.num_rows();
    let end = blizzards
        .row(n - 1)
        .enumerate()
        .find_map(|(j, cell)| {
            if cell.is_empty() {
                Some([n - 1, j])
            } else {
                None
            }
        })
        .expect("start position on last row");
    chart_course(blizzards, start, end).expect("there is a solution")
}

pub fn solve_part2(blizzards: &mut Grid<Blizzard>) -> usize {
    let start = blizzards
        .row(0)
        .enumerate()
        .find_map(|(j, cell)| if cell.is_empty() { Some([0, j]) } else { None })
        .expect("start position on first row");
    let n = blizzards.num_rows();
    let end = blizzards
        .row(n - 1)
        .enumerate()
        .find_map(|(j, cell)| {
            if cell.is_empty() {
                Some([n - 1, j])
            } else {
                None
            }
        })
        .expect("start position on last row");

    let m1 = chart_course(blizzards, start, end).expect("there is a solution");
    let m2 = chart_course(blizzards, end, start).expect("there is a solution");
    let m3 = chart_course(blizzards, start, end).expect("there is a solution");
    m1 + m2 + m3
}

/// Evolves one step in all four directions.
pub fn evolve(grid: &mut Grid<Blizzard>) {
    for i in 0..grid.num_rows() {
        evolve_left(grid, i);
        evolve_right(grid, i);
    }
    for j in 0..grid.num_cols() {
        evolve_up(grid, j);
        evolve_down(grid, j);
    }
}

/// Evolves blizzards blowing left in the given row.
fn evolve_left(grid: &mut Grid<Blizzard>, row: usize) {
    let num_cols = grid.num_cols();
    let wrap = grid[[row, 1]] & Blizzard::LEFT;
    grid[[row, 1]].remove(Blizzard::LEFT);
    for j in 2..num_cols - 1 {
        let bit = grid[[row, j]] & Blizzard::LEFT;
        grid[[row, j]].remove(Blizzard::LEFT);
        grid[[row, j - 1]] |= bit;
    }
    grid[[row, num_cols - 2]] |= wrap;
}

/// Evolves blizzards blowing right in the given row.
fn evolve_right(grid: &mut Grid<Blizzard>, row: usize) {
    let num_cols = grid.num_cols();
    let wrap = grid[[row, num_cols - 2]] & Blizzard::RIGHT;
    grid[[row, num_cols - 2]].remove(Blizzard::RIGHT);
    for j in (1..num_cols - 2).rev() {
        let bit = grid[[row, j]] & Blizzard::RIGHT;
        grid[[row, j]].remove(Blizzard::RIGHT);
        grid[[row, j + 1]] |= bit;
    }
    grid[[row, 1]] |= wrap;
}

/// Evolves blizzards blowing up in the given column.
fn evolve_up(grid: &mut Grid<Blizzard>, column: usize) {
    let num_rows = grid.num_rows();
    let wrap = grid[[1, column]] & Blizzard::UP;
    grid[[1, column]].remove(Blizzard::UP);
    for i in 2..num_rows - 1 {
        let bit = grid[[i, column]] & Blizzard::UP;
        grid[[i, column]].remove(Blizzard::UP);
        grid[[i - 1, column]] |= bit;
    }
    grid[[num_rows - 2, column]] |= wrap;
}

/// Evolves blizzards blowing down in the given column.
fn evolve_down(grid: &mut Grid<Blizzard>, column: usize) {
    let num_rows = grid.num_rows();
    let wrap = grid[[num_rows - 2, column]] & Blizzard::DOWN;
    grid[[num_rows - 2, column]].remove(Blizzard::DOWN);
    for i in (1..num_rows - 2).rev() {
        let bit = grid[[i, column]] & Blizzard::DOWN;
        grid[[i, column]].remove(Blizzard::DOWN);
        grid[[i + 1, column]] |= bit;
    }
    grid[[1, column]] |= wrap;
}

/// Displays the state of the grid in a format expected by the parser.
pub fn display_grid(grid: &Grid<Blizzard>) {
    for i in 0..grid.num_rows() {
        for j in 0..grid.num_cols() {
            print!("{}", grid[[i, j]]);
        }
        println!();
    }
}

pub fn display_bool_grid(grid: &Grid<bool>) {
    for i in 0..grid.num_rows() {
        for j in 0..grid.num_cols() {
            print!("{}", if grid[[i, j]] { '*' } else { '.' });
        }
        println!();
    }
}

/// Parses the input into a grid with blizzards and walls.
///
/// # Errors
///
/// Returns an error if the rows do not all have the same length or if there is an unexpected
/// character.
pub fn parse_input(s: &str) -> Result<Grid<Blizzard>> {
    // XXX Should we verify that the walls only occur on the boundary?  This is not stated
    // explicitly in the puzzle description, but it seems implicit in the description of
    // the "conservation of blizzard energy": where when "a blizzard reaches the wall of the
    // valley, a new blizzard forms on the opposite side of the valley moving in the same
    // direction".  So walls have "opposites".
    let rows: Result<Vec<_>> = s.lines().map(parse_line).collect();
    let rows = rows?;
    let num_cols = rows.first().map_or(0, Vec::len);
    let mut grid = Grid::new(num_cols);
    for row in rows {
        grid.push_row(row)?;
    }
    Ok(grid)
}

fn parse_line(s: &str) -> Result<Vec<Blizzard>> {
    s.chars().map(Blizzard::try_from).collect()
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_part1_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let mut blizzards = parse_input(&input)?;
        let num_minutes = solve_part1(&mut blizzards);
        assert_eq!(num_minutes, 10);
        Ok(())
    }

    #[test]
    fn test_part1_example2() -> Result<()> {
        let input = fs::read_to_string("data/example2")?;
        let mut blizzards = parse_input(&input)?;
        let num_minutes = solve_part1(&mut blizzards);
        assert_eq!(num_minutes, 18);
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let mut blizzards = parse_input(&input)?;
        let num_minutes = solve_part1(&mut blizzards);
        assert_eq!(num_minutes, 257);
        Ok(())
    }

    #[test]
    fn test_part2_example2() -> Result<()> {
        let input = fs::read_to_string("data/example2")?;
        let mut blizzards = parse_input(&input)?;
        let num_minutes = solve_part2(&mut blizzards);
        assert_eq!(num_minutes, 54);
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let mut blizzards = parse_input(&input)?;
        let num_minutes = solve_part2(&mut blizzards);
        assert_eq!(num_minutes, 828);
        Ok(())
    }
}
