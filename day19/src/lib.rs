//! Solutions to [Advent of Code 2022 Day 19](https://adventofcode.com/2022/day/19).

use std::borrow::{Borrow, BorrowMut};
use std::io;
use std::num::ParseIntError;
use std::ops::{Add, AddAssign, Index, IndexMut, Sub, SubAssign};
use std::str::FromStr;

use once_cell::sync::OnceCell;
use rayon::prelude::*;
use regex::Regex;
use thiserror::Error;

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

    /// An error parsing an integer.
    #[error("Error parsing integer")]
    ParseInt(#[from] ParseIntError),

    /// An error parsing a blueprint.
    #[error("Error parsing blueprint")]
    ParseBlueprint(String),
}

/// A specialized [`Result`] type for operations in this crate.
///
/// [`Result`]: std::result::Result
pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ResourceKind {
    Ore = 0,
    Clay = 1,
    Obsidian = 2,
    Geode = 3,
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq)]
pub struct ResourceArray<T>([T; 4]);

pub type ResourceMatrix<T> = ResourceArray<ResourceArray<T>>;

impl<T> Index<ResourceKind> for ResourceArray<T> {
    type Output = T;

    fn index(&self, resouce: ResourceKind) -> &Self::Output {
        &self.0[resouce as usize]
    }
}

impl<T> IndexMut<ResourceKind> for ResourceArray<T> {
    fn index_mut(&mut self, resouce: ResourceKind) -> &mut Self::Output {
        &mut self.0[resouce as usize]
    }
}

impl<T> From<[T; 4]> for ResourceArray<T> {
    fn from(array: [T; 4]) -> Self {
        Self(array)
    }
}

impl<T> From<ResourceArray<T>> for [T; 4] {
    fn from(resource_array: ResourceArray<T>) -> Self {
        resource_array.0
    }
}

impl<T> AsRef<[T]> for ResourceArray<T> {
    fn as_ref(&self) -> &[T] {
        self.0.as_ref()
    }
}

impl<T> AsMut<[T]> for ResourceArray<T> {
    fn as_mut(&mut self) -> &mut [T] {
        self.0.as_mut()
    }
}

impl<T> Borrow<[T]> for ResourceArray<T> {
    fn borrow(&self) -> &[T] {
        self.0.borrow()
    }
}

impl<T> BorrowMut<[T]> for ResourceArray<T> {
    fn borrow_mut(&mut self) -> &mut [T] {
        self.0.borrow_mut()
    }
}

impl<T: Add<Output = T> + Default> Add for ResourceArray<T> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let mut output = Self::default();
        output
            .0
            .iter_mut()
            .zip(self.0.into_iter().zip(other.0.into_iter()))
            .for_each(|(out, (a, b))| *out = a + b);
        output
    }
}

impl<T: AddAssign> AddAssign for ResourceArray<T> {
    fn add_assign(&mut self, other: Self) {
        self.0
            .iter_mut()
            .zip(other.0.into_iter())
            .for_each(|(a, b)| *a += b);
    }
}

impl<T: Sub<Output = T> + Default> Sub for ResourceArray<T> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        let mut output = Self::default();
        output
            .0
            .iter_mut()
            .zip(self.0.into_iter().zip(other.0.into_iter()))
            .for_each(|(out, (a, b))| *out = a - b);
        output
    }
}

impl<T: SubAssign> SubAssign for ResourceArray<T> {
    fn sub_assign(&mut self, other: Self) {
        self.0
            .iter_mut()
            .zip(other.0.into_iter())
            .for_each(|(a, b)| *a -= b);
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Blueprint {
    id: usize,
    costs: ResourceMatrix<usize>,
}

impl FromStr for Blueprint {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        use ResourceKind::*;

        let re = regex!(
            r"(?x)Blueprint\ (?P<id>\d+):\s*
        Each\ ore\ robot\ costs\ (?P<ore_ore>\d+)\ ore.\s*
        Each\ clay\ robot\ costs\ (?P<clay_ore>\d+)\ ore.\s*
        Each\ obsidian\ robot\ costs\ (?P<obsidian_ore>\d+)\ ore\ and\ (?P<obsidian_clay>\d+)\ clay.\s*
        Each\ geode\ robot\ costs\ (?P<geode_ore>\d+)\ ore\ and\ (?P<geode_obsidian>\d+)\ obsidian."
        );
        let caps = re
            .captures(s)
            .ok_or_else(|| Error::ParseBlueprint(s.into()))?;

        let id = caps["id"].parse()?;

        let mut costs = ResourceMatrix::default();

        // Get cost of ore-producing robots.
        let ore_ore = caps["ore_ore"].parse()?;
        costs[Ore][Ore] = ore_ore;

        // Get cost of clay-producing robots.
        let clay_ore = caps["clay_ore"].parse()?;
        costs[Clay][Ore] = clay_ore;

        // Get cost of obsidian-producing robots.
        let obsidian_ore = caps["obsidian_ore"].parse()?;
        costs[Obsidian][Ore] = obsidian_ore;
        let obsidian_clay = caps["obsidian_clay"].parse()?;
        costs[Obsidian][Clay] = obsidian_clay;

        // Get cost of geode-producing robots.
        let geode_ore = caps["geode_ore"].parse()?;
        costs[Geode][Ore] = geode_ore;
        let geode_obsidian = caps["geode_obsidian"].parse()?;
        costs[Geode][Obsidian] = geode_obsidian;

        Ok(Blueprint { id, costs })
    }
}

impl Blueprint {
    /// Returns the maximum number of geodes that can be produced using this blueprint.
    #[must_use]
    pub fn optimize_geodes(&self, time_limit: usize) -> usize {
        optimize(self, time_limit).geodes()
    }

    /// Returns the quality level of the blueprint.
    #[must_use]
    pub fn quality_level(&self, time_limit: usize) -> usize {
        self.id * self.optimize_geodes(time_limit)
    }
}

/// Returns the sum of the quality levels of the blueprints.
#[must_use]
pub fn solve_part1(blueprints: &[Blueprint]) -> usize {
    blueprints
        .par_iter()
        .map(|blueprint| blueprint.quality_level(24))
        .sum()
}

/// Parses the puzzle input as a vector of [`Blueprint`]s.
///
/// # Errors
///
/// Returns [`Error::ParseBlueprint`] if a line of input does not have the right format for a
/// blueprint.  Returns [`Error::ParseInt`] if there is an error parsing an integer.
pub fn parse_input(s: &str) -> Result<Vec<Blueprint>> {
    s.lines().map(str::parse).collect()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Strategy {
    purchases: Vec<Option<ResourceKind>>,
    robots: ResourceArray<usize>,
    resource_balances: ResourceArray<usize>,
    costs: ResourceMatrix<usize>,
    time_limit: usize,
}

impl Strategy {
    fn new(costs: ResourceMatrix<usize>, time_limit: usize) -> Self {
        let mut robots = ResourceArray::default();
        robots[ResourceKind::Ore] = 1;
        Self {
            purchases: Vec::new(),
            robots,
            resource_balances: ResourceArray::default(),
            costs,
            time_limit,
        }
    }

    /// Returns an array indicating which robots are affordable.
    fn affordable_robots(&self) -> ResourceArray<bool> {
        let mut affordable = ResourceArray::default();
        for i in 0..4 {
            affordable.0[i] = self.costs.0[i]
                .0
                .iter()
                .zip(self.resource_balances.0.iter())
                .all(|(a, b)| a <= b);
        }
        affordable
    }

    /// Possibly converts resources into a robot and updates balances accordingly.
    fn update(&mut self, purchase: Option<ResourceKind>) {
        if let Some(kind) = purchase {
            self.resource_balances -= self.costs[kind];
        }
        self.resource_balances += self.robots;
        if let Some(kind) = purchase {
            self.robots[kind] += 1;
        }
        self.purchases.push(purchase);
    }

    /// Undoes the last purchase.
    fn undo(&mut self) -> Option<()> {
        let purchase = self.purchases.pop()?;
        if let Some(kind) = purchase {
            self.robots[kind] -= 1;
            self.resource_balances += self.costs[kind];
        }
        self.resource_balances -= self.robots;
        Some(())
    }

    #[must_use]
    pub fn geodes(&self) -> usize {
        self.resource_balances[ResourceKind::Geode]
    }
}

#[must_use]
pub fn optimize(blueprint: &Blueprint, time_limit: usize) -> Strategy {
    let mut strategy = Strategy::new(blueprint.costs, time_limit);
    optimize_recursive(&mut strategy, ResourceArray::default())
}

#[must_use]
fn optimize_recursive(strategy: &mut Strategy, taboo: ResourceArray<bool>) -> Strategy {
    use ResourceKind::*;

    if strategy.purchases.len() >= strategy.time_limit {
        return strategy.clone();
    }

    let is_affordable = strategy.affordable_robots();

    let mut purchases = Vec::new();
    if is_affordable[Geode] && !taboo[Geode] {
        purchases.push(Some(Geode));
    }
    if is_affordable[Obsidian] && !taboo[Obsidian] {
        purchases.push(Some(Obsidian));
    }
    if is_affordable[Clay] && !taboo[Clay] {
        purchases.push(Some(Clay));
    }
    if is_affordable[Ore] && !taboo[Ore] {
        purchases.push(Some(Ore));
    }
    let mut best = Vec::new();
    for purchase in purchases {
        strategy.update(purchase);
        best.push(optimize_recursive(strategy, ResourceArray::default()));
        strategy.undo();
    }
    strategy.update(None);
    best.push(optimize_recursive(strategy, is_affordable));
    strategy.undo();

    best.into_iter()
        .max_by_key(Strategy::geodes)
        .expect("the list is nonempty")
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_optimize_geodes() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let blueprints = parse_input(&input)?;
        let geodes = blueprints[0].optimize_geodes();
        assert_eq!(geodes, 9);
        let geodes = blueprints[1].optimize_geodes();
        assert_eq!(geodes, 12);
        Ok(())
    }

    #[test]
    fn test_part1_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let blueprints = parse_input(&input)?;
        let quality_sum = solve_part1(&blueprints);
        assert_eq!(quality_sum, 33);
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let blueprints = parse_input(&input)?;
        let quality_sum = solve_part1(&blueprints);
        assert_eq!(quality_sum, 1262);
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
