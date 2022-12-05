//! Solutions to [Advent of Code 2022 Day 5](https://adventofcode.com/2022/day/5).

use std::io;
use std::num::{NonZeroUsize, ParseIntError};
use std::str::FromStr;

use thiserror::Error;

use once_cell::sync::OnceCell;
use regex::Regex;

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

    /// The input was missing a blank line separating the stacks diagram from the instructions.
    #[error("Missing blank line")]
    MissingBlankLine,

    /// A malformed instruction for moving items.
    #[error("Invalid move instruction")]
    BadInstruction(String),

    /// Missing stack numbers in diagram.
    #[error("Invalid stack diagram: missing stack numbers")]
    MissingStackNumbers,

    /// Error parsing an integer.
    #[error("Error parsing integer")]
    ParseInt(#[from] ParseIntError),

    /// Unexpected stack number.
    #[error("Got stack number {0}, expected {1}")]
    UnexpectedStackNumber(usize, usize),

    /// Invalid stack diagram.
    #[error("Invalid stack diagram")]
    InvalidStackDiagram,

    /// Stack index too large.
    #[error("Stack index out of range: got {0}, maximum {1}")]
    StackIndex(usize, usize),

    /// Attempt to pop from an empty stack.
    #[error("Attempt to pop from empty stack: {0}")]
    StackEmpty(usize),
}

/// A specialized [`Result`] type for operations in this crate.
///
/// [`Result`]: std::result::Result
pub type Result<T> = std::result::Result<T, Error>;

pub type StackIdx = NonZeroUsize;

/// An instruction for moving some number of items from one stack to another.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Move {
    /// How many items to move.
    quantity: usize,

    /// The stack from which to move the items.
    source: StackIdx,

    /// The stack to which to move the items.
    dest: StackIdx,
}

impl Move {
    /// Creates a new move instruction.
    #[must_use]
    pub fn new(quantity: usize, source: StackIdx, dest: StackIdx) -> Self {
        Self {
            quantity,
            source,
            dest,
        }
    }
}

impl FromStr for Move {
    type Err = Error;

    /// Parses a single instruction for moving items.
    ///
    /// The instruction should have the form:
    ///
    /// ```text
    ///     move <QUANTITY> from <SOURCE> to <DEST>
    /// ```
    fn from_str(s: &str) -> Result<Self> {
        let re = regex!(r"^move (?P<quantity>\d+) from (?P<source>\d+) to (?P<dest>\d+)$");
        let caps = re
            .captures(s)
            .ok_or_else(|| Error::BadInstruction(s.into()))?;
        let quantity = caps["quantity"]
            .parse()
            .expect("digits can be parsed as an int");
        let source = caps["source"]
            .parse()
            .expect("digits can be parsed as an int");
        let dest = caps["dest"]
            .parse()
            .expect("digits can be parsed as an int");
        let instruction = Self {
            quantity,
            source,
            dest,
        };
        Ok(instruction)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Item(char);

impl Item {
    #[must_use]
    pub fn to_char(&self) -> char {
        self.0
    }
}

#[derive(Debug, Clone)]
pub struct Stacks {
    stacks: Vec<Vec<Item>>,
}

impl Stacks {
    #[must_use]
    pub fn peek(&self) -> Vec<Option<Item>> {
        self.stacks
            .iter()
            .map(|stack| stack.last().copied())
            .collect()
    }

    /// Returns a [`String`] concatenating the labels of the items on the tops of the stacks.
    ///
    /// Empty stacks are indicated with an ascii space character (`' '`).
    #[must_use]
    pub fn top_of_stacks(&self) -> String {
        self.peek()
            .into_iter()
            .map(|opt| opt.map_or(' ', |item| item.to_char()))
            .collect()
    }

    fn verify_stack_index(&self, i: StackIdx) -> Result<()> {
        if i.get() > self.stacks.len() {
            return Err(Error::StackIndex(i.get(), self.stacks.len()));
        }
        Ok(())
    }

    fn verify_depth(&self, i: StackIdx, n: usize) -> Result<()> {
        if self.stacks[i.get() - 1].len() < n {
            return Err(Error::StackEmpty(i.get()));
        }
        Ok(())
    }

    /// Transfers items between two stacks according to an instruction.
    ///
    /// Items are transfered one at a time, starting from the top of the source stack, thus
    /// reversing their relative orders in the destination stack.
    ///
    /// # Errors
    ///
    /// Returns [`Error`] if the instruction is illegal: either the source or destination stack
    /// numbers are out of bounds, or if the source stack contains fewer items than the quantity to
    /// be moved.  In these cases, the stack is not modified.
    pub fn transfer(&mut self, instruction: &Move) -> Result<()> {
        // Verify that the instruction is valid before modifying `self`.  Otherwise, we might start
        // modifying `self` and then exit with an error before completing the instruction, leaving
        // `self` in an unexpected state which could include dropping items.
        self.verify_stack_index(instruction.source)?;
        self.verify_stack_index(instruction.dest)?;
        self.verify_depth(instruction.source, instruction.quantity)?;

        for _ in 0..instruction.quantity {
            // None of the following operations will panic because we have already verified the
            // indices are in bounds and the stack is long enough.
            let source = &mut self.stacks[instruction.source.get() - 1];
            let item = source.pop().expect("the stack is non-empty");
            let dest = &mut self.stacks[instruction.dest.get() - 1];
            dest.push(item);
        }
        Ok(())
    }

    /// Transfers items between two stacks according to an instruction.
    ///
    /// Items are transfered all at once, preserving their relative orders from the source stack in
    /// the destination stack.
    ///
    /// # Errors
    ///
    /// Returns [`Error`] if the instruction is illegal: either the source or destination stack
    /// numbers are out of bounds, or if the source stack contains fewer items than the quantity to
    /// be moved.  In these cases, the stack is not modified.
    pub fn transfer_many(&mut self, instruction: &Move) -> Result<()> {
        // See comment in `transfer()` regarding looking before we leap.
        self.verify_stack_index(instruction.source)?;
        self.verify_stack_index(instruction.dest)?;
        self.verify_depth(instruction.source, instruction.quantity)?;

        // None of the following operations will panic because we have already verified the
        // indices are in bounds and the stack is long enough.
        let source = &mut self.stacks[instruction.source.get() - 1];
        let items = source.split_off(source.len() - instruction.quantity);
        let dest = &mut self.stacks[instruction.dest.get() - 1];
        dest.extend(items);
        Ok(())
    }
}

pub fn solve_part1(stacks: &mut Stacks, instructions: &[Move]) -> Result<String> {
    for inst in instructions {
        stacks.transfer(inst)?;
    }
    let items = stacks.top_of_stacks();
    Ok(items)
}

pub fn solve_part2(stacks: &mut Stacks, instructions: &[Move]) -> Result<String> {
    for inst in instructions {
        stacks.transfer_many(inst)?;
    }
    let items = stacks.top_of_stacks();
    Ok(items)
}

pub fn parse_input(s: &str) -> Result<(Stacks, Vec<Move>)> {
    let (diagram, moves) = s.split_once("\n\n").ok_or(Error::MissingBlankLine)?;
    let stacks = parse_stacks_diagram(diagram)?;
    let instructions = parse_instructions(moves)?;
    Ok((stacks, instructions))
}

/// Parses a list of instructions.
fn parse_instructions(s: &str) -> Result<Vec<Move>> {
    s.lines().map(str::parse).collect()
}

/// Parses a diagram of stacks of items.
///
/// # Panics
///
/// Panics if a line of the diagram has more items depicted than there are numbered stacks of items.
fn parse_stacks_diagram(s: &str) -> Result<Stacks> {
    // Iterate over the lines of the diagram in reverse order so that we push onto the stacks in
    // reverse order.
    let mut lines = s.lines().rev();
    let first_line = lines.next().ok_or(Error::MissingStackNumbers)?;
    let n = parse_stack_numbers(first_line)?;

    let mut stacks = vec![Vec::new(); n];
    // Once a stack is finished, it cannot later have another item added.
    let mut finished = vec![false; n];

    let re = regex!(r"(\[(?P<item_label>[[:upper:]])\]|   )( |$)");

    for line in lines {
        for (i, caps) in re.captures_iter(line).enumerate() {
            if let Some(m) = caps.name("item_label") {
                let c = m
                    .as_str()
                    .chars()
                    .next()
                    .expect("item labels are not empty");
                let item = Item(c);
                if finished[i] {
                    return Err(Error::InvalidStackDiagram);
                }
                stacks[i].push(item);
            } else {
                // No item on this stack, mark it as finished so that we cannot later try to add
                // another item to it.
                finished[i] = true;
            }
        }
    }
    Ok(Stacks { stacks })
}

/// Parses a row of whitespace-separated numbers, required to be consecutive starting at 1.
///
/// Returns [`Error::UnexpectedStackNumber`] if an out-of-order number is found, and
/// [`Error::ParseInt`] if a field cannot be parsed as an integer.
fn parse_stack_numbers(s: &str) -> Result<usize> {
    let mut n = 0;
    for (idx, field) in s.split_ascii_whitespace().enumerate() {
        let stack_num: usize = field.parse()?;
        if stack_num != idx + 1 {
            return Err(Error::UnexpectedStackNumber(stack_num, idx));
        }
        n += 1;
    }
    Ok(n)
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_part1_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let (mut stacks, instructions) = parse_input(&input)?;
        let top_of_stacks = solve_part1(&mut stacks, &instructions)?;
        assert_eq!(top_of_stacks, "CMZ");
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let (mut stacks, instructions) = parse_input(&input)?;
        let top_of_stacks = solve_part1(&mut stacks, &instructions)?;
        assert_eq!(top_of_stacks, "ZRLJGSCTR");
        Ok(())
    }

    #[test]
    fn test_part2_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let (mut stacks, instructions) = parse_input(&input)?;
        let top_of_stacks = solve_part2(&mut stacks, &instructions)?;
        assert_eq!(top_of_stacks, "MCD");
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let (mut stacks, instructions) = parse_input(&input)?;
        let top_of_stacks = solve_part2(&mut stacks, &instructions)?;
        assert_eq!(top_of_stacks, "PRTTGRFPB");
        Ok(())
    }
}
