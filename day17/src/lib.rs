//! Solutions to [Advent of Code 2022 Day 17](https://adventofcode.com/2022/day/17).

use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;
use std::io;
use std::iter::Cycle;
use std::vec;

use thiserror::Error;

// const FILLED: char = '▓';
// const EMPTY: char = '░';
const FILLED: char = '#';
const EMPTY: char = '.';

/// The error type for operations in this crate.
#[derive(Debug, Error)]
pub enum Error {
    /// An underlying [`io::Error`].
    #[error("I/O error")]
    Io(#[from] io::Error),

    /// An error parsing input
    #[error("Error parsing input: illegal character: '{0}'")]
    Parse(char),
}

/// A specialized [`Result`] type for operations in this crate.
///
/// [`Result`]: std::result::Result
pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Shift {
    Left,
    Right,
}

impl TryFrom<char> for Shift {
    type Error = Error;

    fn try_from(c: char) -> Result<Self> {
        match c {
            '<' => Ok(Shift::Left),
            '>' => Ok(Shift::Right),
            _ => Err(Error::Parse(c)),
        }
    }
}

/// Parses input into a vector of [`Shift`]s.
///
/// # Errors
///
/// Returns [`Error::Parse`] if any character other than `'<'` or `'>'` is encountered, ignoring
/// leading and trailing whitespace.
pub fn parse_input(s: &str) -> Result<Vec<Shift>> {
    s.trim().chars().map(Shift::try_from).collect()
}

fn write_bool_slice(f: &mut fmt::Formatter<'_>, slice: &[bool]) -> fmt::Result {
    let s: String = slice
        .iter()
        .map(|&b| if b { FILLED } else { EMPTY })
        .collect();
    writeln!(f, "{s}")?;
    Ok(())
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq)]
pub struct Rock {
    cursor: [[bool; 4]; 4],
}

impl fmt::Display for Rock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for row in self.cursor.iter().rev() {
            write_bool_slice(f, row)?;
        }
        Ok(())
    }
}

pub const ROCK_SHAPES: [Rock; 5] = [
    // 3: ░░░░
    // 2: ░░░░
    // 1: ░░░░
    // 0: ▓▓▓▓
    Rock {
        cursor: [
            [true, true, true, true],
            [false, false, false, false],
            [false, false, false, false],
            [false, false, false, false],
        ],
    },
    // 3: ░░░░
    // 2: ░▓░░
    // 1: ▓▓▓░
    // 0: ░▓░░
    Rock {
        cursor: [
            [false, true, false, false],
            [true, true, true, false],
            [false, true, false, false],
            [false, false, false, false],
        ],
    },
    //3: ░░░░
    //2: ░░▓░
    //1: ░░▓░
    //0: ▓▓▓░
    Rock {
        cursor: [
            [true, true, true, false],
            [false, false, true, false],
            [false, false, true, false],
            [false, false, false, false],
        ],
    },
    // 3: ▓░░░
    // 2: ▓░░░
    // 1: ▓░░░
    // 0: ▓░░░
    Rock {
        cursor: [
            [true, false, false, false],
            [true, false, false, false],
            [true, false, false, false],
            [true, false, false, false],
        ],
    },
    // 3: ░░░░
    // 2: ░░░░
    // 1: ▓▓░░
    // 0: ▓▓░░
    Rock {
        cursor: [
            [true, true, false, false],
            [true, true, false, false],
            [false, false, false, false],
            [false, false, false, false],
        ],
    },
];

/// A game board with floor as row `0` and walls in columns `0` and `N - 4`.
#[derive(Debug, Clone)]
pub struct Board<const N: usize> {
    rows: Vec<[bool; N]>,
    jets: Cycle<vec::IntoIter<Shift>>,
    rocks: Cycle<vec::IntoIter<Rock>>,
    jet_period: usize,
    rock_period: usize,
    jet_count: usize,
    rock_count: usize,
}

impl<const N: usize> fmt::Display for Board<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for row in self.rows.iter().rev() {
            write_bool_slice(f, &row[..N - 3])?;
        }
        Ok(())
    }
}

impl<const N: usize> Board<N> {
    /// Returns a new board with only a rocky floor.
    #[must_use]
    pub fn new(jets: Vec<Shift>, rocks: Vec<Rock>) -> Self {
        let floor = [true; N];
        let rows = vec![floor];
        let jet_period = jets.len();
        let rock_period = rocks.len();
        let jets = jets.into_iter().cycle();
        let rocks = rocks.into_iter().cycle();
        Self {
            rows,
            jets,
            rocks,
            jet_period,
            rock_period,
            jet_count: 0,
            rock_count: 0,
        }
    }

    /// Adds a new row with no rocks except walls in columns `0` and `N-4`.
    pub fn add_row(&mut self) {
        let mut row = [false; N];
        // Add borders in columns 0 and `N - 4`.
        row[0] = true;
        row[N - 4] = true;
        self.rows.push(row);
    }

    /// Returns the highest row with a filled cell in columns 1 through `N - 5` inclusive.
    #[must_use]
    pub fn find_peak(&self) -> usize {
        self.rows
            .iter()
            .enumerate()
            .rev()
            .find_map(|(i, row)| {
                if row[1..N - 4].iter().any(|&t| t) {
                    Some(i)
                } else {
                    None
                }
            })
            .expect("The board has a rock floor")
    }

    /// Pads with empty rows and returns the row index for the bottom of the cursor.
    ///
    /// This adds enough empty rows to start dropping the next rock and it returns the row index of
    /// the bottom row of the rock cursor.
    #[must_use]
    pub fn pad(&mut self) -> usize {
        let k = self.find_peak();
        let l = self.rows.len();
        (l..k + 8).for_each(|_| self.add_row());
        k + 4
    }

    /// Returns `true` iff the given rock fits with its cursor in the given `row` and `column`.
    ///
    /// The rock fits if none of its filled cells overlap a filled cell of the board.
    #[must_use]
    pub fn fits(&self, rock: Rock, row: usize, column: usize) -> bool {
        // Iterate over the rows of the rock cursor zipped with the rows of the board starting at
        // row index `row`.  For each pair of row, iterate over the columns of that row of the rock
        // cursor zipped with the columns of the corresponding row of the board, where the `0`th
        // column of the rock cursor is aligned with column index `column` in the board.  Returns
        // `true` iff no aligned cell in the rock cursor and its corresponding cell in the board
        // are both filled (`true`).
        !rock
            .cursor
            .iter()
            .zip(self.rows[row..].iter())
            .flat_map(|(rock, board)| rock.iter().zip(board[column..].iter()))
            .any(|(r, b)| r & b)
    }

    /// Places a rock on the board at the given position of the lower left corner of the rock
    /// cursor.
    fn place_rock(&mut self, rock: Rock, row: usize, column: usize) {
        rock.cursor
            .iter()
            .zip(self.rows[row..].iter_mut())
            .for_each(|(rock, board)| {
                rock.iter()
                    .zip(board[column..].iter_mut())
                    .for_each(|(r, b)| {
                        *b |= r;
                    });
            });
    }

    fn drop_rock(&mut self, rock: Rock) {
        let k = self.pad();
        // The bottom left corner of the cursor is initally in column 3 of row k.
        let mut cursor_row = k;
        let mut cursor_col = 3;
        loop {
            // The jets of air blow the rock.
            let shift = self.jets.next().expect("the jets cycle endlessly");
            self.jet_count += 1;
            let (r, c) = match shift {
                Shift::Left => (cursor_row, cursor_col - 1),
                Shift::Right => (cursor_row, cursor_col + 1),
            };
            if self.fits(rock, r, c) {
                cursor_row = r;
                cursor_col = c;
            }

            // The rock falls.
            let r = cursor_row - 1;
            let c = cursor_col;
            if !self.fits(rock, r, c) {
                break;
            }
            cursor_row = r;
            cursor_col = c;
        }
        self.place_rock(rock, cursor_row, cursor_col);
    }

    pub fn do_round(&mut self) {
        let rock = self.rocks.next().expect("the rocks cycle endlessly");
        self.rock_count += 1;
        self.drop_rock(rock);
        /*
        dbg!(
            self.jet_count,
            self.jet_count % 10091,
            self.rock_count,
            self.rock_count % 5
        );
        */
    }

    pub fn do_rounds(&mut self, num_rounds: usize) {
        (0..num_rounds).for_each(|_| {
            self.do_round();
        });
    }

    #[must_use]
    pub fn state(&self) -> State<N> {
        let top_floor = self.find_floor();
        let rows = self.rows[top_floor..].to_vec();
        State {
            rows,
            jet_count: self.jet_count % self.jet_period,
            rock_count: self.rock_count % self.rock_period,
        }
    }

    /// Finds the highest row of all rocks.
    #[must_use]
    pub fn find_floor(&self) -> usize {
        self.rows
            .iter()
            .enumerate()
            .rev()
            .find_map(|(k, row)| {
                if row[1..N - 4].iter().all(|&t| t) {
                    Some(k)
                } else {
                    None
                }
            })
            .expect("The board has a rocky floor")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct State<const N: usize> {
    rows: Vec<[bool; N]>,
    jet_count: usize,
    rock_count: usize,
}

#[must_use]
pub fn solve_part1(shifts: Vec<Shift>) -> usize {
    let rocks = ROCK_SHAPES.to_vec();
    let mut board = Board::<12>::new(shifts, rocks);
    board.do_rounds(2022);
    board.find_peak()
}

#[must_use]
pub fn solve_part2(shifts: Vec<Shift>, num_rounds: usize) -> Option<usize> {
    let rocks = ROCK_SHAPES.to_vec();
    let mut board = Board::<12>::new(shifts, rocks);
    let mut states = HashMap::new();
    for round in 1.. {
        board.do_round();
        let state = board.state();
        let height = board.find_peak();
        let (last_round, last_height) = states.entry(state).or_insert((round, height));
        if *last_round < round {
            let period = round - *last_round;
            let periods = (num_rounds - round) / period;
            let remainder = (num_rounds - round) % period;
            if remainder == 0 {
                return Some(height + periods * (height - *last_height));
            }
            *last_round = round;
            *last_height = height;
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_part1_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let shifts = parse_input(&input)?;
        let height = solve_part1(shifts);
        assert_eq!(height, 3068);
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let shifts = parse_input(&input)?;
        let height = solve_part1(shifts);
        assert_eq!(height, 3071);
        Ok(())
    }

    /*
    #[test]
    fn test_part2_example() -> Result<()> {
        todo!();
    }
    */

    #[test]
    fn test_part2_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let shifts = parse_input(&input)?;
        let height = solve_part2(shifts, 1_000_000_000_000);
        assert_eq!(height, Some(1523615160362));
        Ok(())
    }
}
