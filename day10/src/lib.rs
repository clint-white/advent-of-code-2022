//! Solutions to [Advent of Code 2022 Day 10](https://adventofcode.com/2022/day/10).

use std::io;
use std::iter::Fuse;
use std::num::ParseIntError;
use std::str::FromStr;

use thiserror::Error;

/// The error type for operations in this crate.
#[derive(Debug, Error)]
pub enum Error {
    /// An underlying [`io::Error`].
    #[error("I/O error")]
    Io(#[from] io::Error),

    /// An underlying [`ParseIntError`].
    #[error("Error parsing integer")]
    ParseInt(#[from] ParseIntError),

    /// Illegal instruction.
    #[error("Illegal instruction: '{0}'")]
    IllegalInstruction(String),
}

/// A specialized [`Result`] type for operations in this crate.
///
/// [`Result`]: std::result::Result
pub type Result<T> = std::result::Result<T, Error>;

/// CPU instructions
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Instruction {
    Noop,
    AddX(i64),
}

impl FromStr for Instruction {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        if s == "noop" {
            return Ok(Self::Noop);
        }
        if let Some(("addx", arg)) = s.split_once(' ') {
            return Ok(Self::AddX(arg.parse()?));
        }
        Err(Error::IllegalInstruction(s.into()))
    }
}

#[derive(Debug, Default, Copy, Clone)]
pub struct Cpu;

impl Cpu {
    #[must_use]
    pub fn new() -> Self {
        Self {}
    }

    pub fn execute<I, E>(self, program: I) -> Executor<E>
    where
        I: IntoIterator<IntoIter = E, Item = Instruction>,
        E: Iterator<Item = Instruction>,
    {
        Executor {
            x: 1,
            program: program.into_iter().fuse(),
            executing: Some((Instruction::Noop, 0)),
        }
    }
}

pub struct Executor<I> {
    x: i64,
    program: Fuse<I>,
    executing: Option<(Instruction, u8)>,
}

impl<I> Executor<I>
where
    I: Iterator<Item = Instruction>,
{
    /// Fetch the next instruction to execute and the number of cycles it requires to execute.
    fn fetch(&mut self) {
        self.executing = self.program.next().map(|instruction| {
            let count = match instruction {
                Instruction::Noop => 1,
                Instruction::AddX(_) => 2,
            };
            (instruction, count - 1)
        });
    }
}

impl<I: Iterator<Item = Instruction>> Iterator for Executor<I> {
    type Item = i64;

    fn next(&mut self) -> Option<Self::Item> {
        let (instruction, count) = self.executing.take()?;
        if count == 0 {
            match instruction {
                Instruction::Noop => (),
                Instruction::AddX(arg) => self.x += arg,
            }
            self.fetch();
        } else {
            self.executing = Some((instruction, count - 1));
        }
        Some(self.x)
    }
}

/// Returns the signal strength during cycle `t` with given `X` register value.
///
/// Note that the puzzle counts cycles starting with 1, while we enumerate cycles from 0.  This
/// function adjusts for that and expects `t` in 0-up indexing.
#[must_use]
pub fn signal_strength(t: usize, x: i64) -> i64 {
    (t + 1) as i64 * x
}

/// Parses program text into a vector of instructions.
///
/// # Errors
///
/// Returns an error if an illegal instruction is encountered or there was an error parsing an
/// integer for the `addx` instruction.
pub fn parse_input(s: &str) -> Result<Vec<Instruction>> {
    s.lines().map(str::parse).collect()
}

#[must_use]
pub fn solve_part1(instructions: &[Instruction]) -> i64 {
    let ins_iter = instructions.iter().copied();
    let cpu = Cpu::new();
    cpu.execute(ins_iter)
        .enumerate()
        .skip(19)
        .step_by(40)
        .take(6)
        .map(|(i, x)| signal_strength(i, x))
        .sum()
}

pub struct Crt<I> {
    executor: Executor<I>,
}

impl<I> Crt<I>
where
    I: Iterator<Item = Instruction>,
{
    const WIDTH: usize = 40;
    const HEIGHT: usize = 6;
    const LIT: char = '█';
    const DARK: char = ' ';

    pub fn new(cpu: Cpu, instructions: I) -> Self {
        Self {
            executor: cpu.execute(instructions),
        }
    }

    pub fn render(&mut self) -> String {
        let mut lines = Vec::new();
        (0..Self::HEIGHT).for_each(|_| {
            let line: String = self
                .executor
                .by_ref()
                .take(Self::WIDTH)
                .enumerate()
                .map(|(pixel, sprite)| {
                    if (pixel as i64 - sprite).abs() <= 1 {
                        Self::LIT
                    } else {
                        Self::DARK
                    }
                })
                .collect();
            lines.push(line);
        });
        lines.join("\n")
    }
}

#[must_use]
pub fn solve_part2(instructions: &[Instruction]) -> String {
    let ins_iter = instructions.iter().copied();
    let cpu = Cpu::new();
    let mut crt = Crt::new(cpu, ins_iter);
    crt.render()
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_part1_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let instructions = parse_input(&input)?;
        let s = solve_part1(&instructions);
        assert_eq!(s, 13140);
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let instructions = parse_input(&input)?;
        let s = solve_part1(&instructions);
        assert_eq!(s, 13440);
        Ok(())
    }

    #[test]
    fn test_part2_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let instructions = parse_input(&input)?;
        let output = solve_part2(&instructions);
        let expected = fs::read_to_string("data/example-part2-output")?;
        assert_eq!(output, expected);
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let instructions = parse_input(&input)?;
        let output = solve_part2(&instructions);
        // PBZGRAZA
        let expected = fs::read_to_string("data/input-part2-output")?;
        assert_eq!(output, expected);
        Ok(())
    }
}
