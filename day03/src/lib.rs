//! Advent of Code 2022 Day 3

use std::collections::HashSet;
use std::fmt;
use std::io;
use std::str::FromStr;

use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error("I/O error")]
    Io(#[from] io::Error),

    #[error("Not an ascii alphabetic byte: '0x{0:02}'")]
    NotAsciiAlphabetic(u8),

    #[error("Input line had odd length")]
    OddLengthLine,

    #[error("Intersection of rucksack compartments of size {0}, expected 1")]
    InvalidIntersection(usize),
}

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Item(u8);

impl Item {
    /// Returns a new `Item` if `value` is ascii alphabetic, else `None`.
    #[must_use]
    pub const fn new(value: u8) -> Option<Self> {
        if value.is_ascii_alphabetic() {
            Some(Self(value))
        } else {
            None
        }
    }

    /// Returns the priority of this `Item`.
    ///
    /// # Examples
    ///
    /// ```
    /// use day03::Item;
    ///
    /// let item = Item::new(b'a').unwrap();
    /// assert_eq!(item.priority(), 1);
    ///
    /// let item = Item::new(b'z').unwrap();
    /// assert_eq!(item.priority(), 26);
    ///
    /// let item = Item::new(b'A').unwrap();
    /// assert_eq!(item.priority(), 27);
    ///
    /// let item = Item::new(b'Z').unwrap();
    /// assert_eq!(item.priority(), 52);
    /// ```
    #[must_use]
    pub fn priority(&self) -> u32 {
        if self.0.is_ascii_lowercase() {
            (self.0 - b'a' + 1).into()
        } else {
            (self.0 - b'A' + 27).into()
        }
    }
}

impl From<Item> for char {
    fn from(item: Item) -> Self {
        item.0.into()
    }
}

impl fmt::Display for Item {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", char::from(*self))
    }
}

#[derive(Debug, Clone)]
pub struct Rucksack {
    items: Vec<Item>,
}

impl Rucksack {
    /// Returns an iterator over the contents of the first compartment.
    pub fn left_compartment(&self) -> impl Iterator<Item = Item> + '_ {
        self.items[..self.items.len() / 2].iter().copied()
    }

    /// Returns an iterator over the contents of the second compartment.
    pub fn right_compartment(&self) -> impl Iterator<Item = Item> + '_ {
        self.items[self.items.len() / 2..].iter().copied()
    }

    /// Returns the set of items as a [`HashSet`].
    #[must_use]
    pub fn to_set(&self) -> HashSet<Item> {
        self.items.iter().copied().collect()
    }

    /// Returns the set of items in both compartments.
    #[must_use]
    pub fn common_items(&self) -> HashSet<Item> {
        let left_set: HashSet<_> = self.left_compartment().collect();
        let right_set: HashSet<_> = self.right_compartment().collect();
        &left_set & &right_set
    }
}

impl FromStr for Rucksack {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        let bytes = s.as_bytes();
        if bytes.len() % 2 != 0 {
            return Err(Error::OddLengthLine);
        }
        let items: Result<Vec<_>> = bytes
            .iter()
            .map(|&b| Item::new(b).ok_or_else(|| Error::NotAsciiAlphabetic(b)))
            .collect();
        let items = items?;
        Ok(Self { items })
    }
}

pub fn read_input(s: &str) -> Result<Vec<Rucksack>> {
    let mut sacks = Vec::new();
    for line in s.lines() {
        let sack = line.parse()?;
        sacks.push(sack);
    }
    Ok(sacks)
}

pub fn solve_part1(sacks: &[Rucksack]) -> Result<u32> {
    let mut total_priority = 0;
    for sack in sacks {
        let common = sack.common_items();
        let item = first_and_only(common)?;
        total_priority += item.priority();
    }
    Ok(total_priority)
}

pub fn solve_part2(sacks: &[Rucksack]) -> Result<u32> {
    let mut total_priority = 0;
    for group in sacks.chunks_exact(3) {
        let items_a = group[0].to_set();
        let items_b = group[1].to_set();
        let items_c = group[2].to_set();
        let intersection = &(&items_a & &items_b) & &items_c;
        let item = first_and_only(intersection)?;
        total_priority += item.priority();
    }
    Ok(total_priority)
}

/// Checks that an iterator yields only one element before stopping and returns that element.
fn first_and_only<I, T, J>(i: I) -> Result<T>
where
    I: IntoIterator<Item = T, IntoIter = J>,
    J: Iterator<Item = T> + ExactSizeIterator,
{
    let mut elts = i.into_iter();
    let item = elts.next().ok_or_else(|| Error::InvalidIntersection(0))?;
    let remaining = elts.len();
    if remaining > 0 {
        return Err(Error::InvalidIntersection(1 + remaining));
    }
    Ok(item)
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_part1_example() -> Result<()> {
        let s = fs::read_to_string("data/example")?;
        let rucksacks = read_input(&s)?;
        let priority = solve_part1(&rucksacks)?;
        assert_eq!(priority, 157);
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let s = fs::read_to_string("data/input")?;
        let rucksacks = read_input(&s)?;
        let priority = solve_part1(&rucksacks)?;
        assert_eq!(priority, 7701);
        Ok(())
    }

    #[test]
    fn test_part2_example() -> Result<()> {
        let s = fs::read_to_string("data/example")?;
        let rucksacks = read_input(&s)?;
        let priority = solve_part2(&rucksacks)?;
        assert_eq!(priority, 70);
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let s = fs::read_to_string("data/input")?;
        let rucksacks = read_input(&s)?;
        let priority = solve_part2(&rucksacks)?;
        assert_eq!(priority, 2644);
        Ok(())
    }
}
