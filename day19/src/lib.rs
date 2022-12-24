//! Solutions to [Advent of Code 2022 Day 19](https://adventofcode.com/2022/day/19).

use std::borrow::{Borrow, BorrowMut};
use std::cmp::Ordering;
use std::fmt;
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

impl<T> ResourceArray<T> {
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.0.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.0.iter_mut()
    }
}

impl<T: Ord> ResourceArray<T> {
    /// Returns `true` iff every element of `self` is greater than or equal to the corresponding
    /// element of `other`.
    pub fn majorizes(&self, other: &Self) -> bool {
        self.iter().zip(other.iter()).all(|(a, b)| a >= b)
    }

    /// Returns `true` iff every element of `self` is less than or equal to the corresponding
    /// element of `other`.
    pub fn minorizes(&self, other: &Self) -> bool {
        self.iter().zip(other.iter()).all(|(a, b)| a <= b)
    }
}

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
            .iter_mut()
            .zip(self.into_iter().zip(other.into_iter()))
            .for_each(|(out, (a, b))| *out = a + b);
        output
    }
}

impl<T: AddAssign> AddAssign for ResourceArray<T> {
    fn add_assign(&mut self, other: Self) {
        self.iter_mut()
            .zip(other.into_iter())
            .for_each(|(a, b)| *a += b);
    }
}

impl<T: Sub<Output = T> + Default> Sub for ResourceArray<T> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        let mut output = Self::default();
        output
            .iter_mut()
            .zip(self.into_iter().zip(other.into_iter()))
            .for_each(|(out, (a, b))| *out = a - b);
        output
    }
}

impl<T: SubAssign> SubAssign for ResourceArray<T> {
    fn sub_assign(&mut self, other: Self) {
        self.iter_mut()
            .zip(other.into_iter())
            .for_each(|(a, b)| *a -= b);
    }
}

impl<T> IntoIterator for ResourceArray<T> {
    type Item = T;

    type IntoIter = std::array::IntoIter<T, 4>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
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
        use ResourceKind::{Clay, Geode, Obsidian, Ore};

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
        optimize_breadth_first(self, time_limit, 1_000).map_or(0, |state| state.geodes())
    }

    /// Returns the quality level of the blueprint.
    #[must_use]
    pub fn quality_level(&self, time_limit: usize) -> usize {
        self.id * self.optimize_geodes(time_limit)
    }

    /// Returns the id of this blueprint.
    #[must_use]
    pub fn id(&self) -> usize {
        self.id
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

#[must_use]
pub fn solve_part2(blueprints: &[Blueprint]) -> usize {
    blueprints
        .par_iter()
        .take(3)
        .map(|blueprint| blueprint.optimize_geodes(32))
        .product()
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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct State {
    resources: ResourceArray<usize>,
    robots: ResourceArray<usize>,
}

impl Default for State {
    fn default() -> Self {
        let mut robots = ResourceArray::default();
        robots[ResourceKind::Ore] = 1;
        Self {
            resources: ResourceArray::default(),
            robots,
        }
    }
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "State[ resources: ")?;
        for n in self.resources.iter() {
            write!(f, "{n} ")?;
        }
        write!(f, ", robots: ")?;
        for n in self.robots.iter() {
            write!(f, "{n} ")?;
        }
        write!(f, "]")
    }
}

impl Ord for State {
    fn cmp(&self, other: &Self) -> Ordering {
        use ResourceKind::{Clay, Geode, Obsidian, Ore};
        self.robots[Geode]
            .cmp(&other.robots[Geode])
            .then_with(|| self.resources[Geode].cmp(&other.resources[Geode]))
            .then_with(|| self.robots[Obsidian].cmp(&other.robots[Obsidian]))
            .then_with(|| self.resources[Obsidian].cmp(&other.resources[Obsidian]))
            .then_with(|| self.robots[Clay].cmp(&other.robots[Clay]))
            .then_with(|| self.resources[Clay].cmp(&other.resources[Clay]))
            .then_with(|| self.robots[Ore].cmp(&other.robots[Ore]))
            .then_with(|| self.resources[Ore].cmp(&other.resources[Ore]))
    }
}

impl PartialOrd for State {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl State {
    /// Increases the number of each resource by the number of the corresponding robot.
    pub fn appreciate(&mut self) {
        self.resources += self.robots;
    }

    /// Returns a new state by exchasing some resources to purchases a robot.  Also generates new
    /// resources from existing robots.
    #[must_use]
    pub fn buy_robot(&self, kind: ResourceKind, costs: &ResourceMatrix<usize>) -> Option<Self> {
        if self.resources.majorizes(&costs[kind]) {
            let mut robots = self.robots;
            robots[kind] += 1;
            let state = Self {
                // Deduct the cost of the new robot, and add in more resources produced in one
                // minute by each of the existing robots.
                resources: self.resources - costs[kind] + self.robots,
                robots,
            };
            Some(state)
        } else {
            None
        }
    }

    /// Returns the number of the given kind of resource.
    #[must_use]
    pub fn num_resource(&self, kind: ResourceKind) -> usize {
        self.resources[kind]
    }

    /// Returns the number of geodes.
    #[must_use]
    pub fn geodes(&self) -> usize {
        self.num_resource(ResourceKind::Geode)
    }

    /// Returns `true` iff `self` has at least as much of every resource and robot type as `other`.
    #[must_use]
    pub fn dominates(&self, other: &Self) -> bool {
        self.resources.majorizes(&other.resources) && self.robots.majorizes(&other.robots)
    }
}

/// Advances a state by one unit of time.
///
/// Returns all possible future states at one time unit later.
fn advance(mut state: State, costs: &ResourceMatrix<usize>) -> Vec<State> {
    use ResourceKind::{Clay, Geode, Obsidian, Ore};

    let mut output = Vec::new();
    if let Some(s) = state.buy_robot(Geode, costs) {
        output.push(s);
    }
    if let Some(s) = state.buy_robot(Obsidian, costs) {
        output.push(s);
    }
    if let Some(s) = state.buy_robot(Clay, costs) {
        output.push(s);
    }
    if let Some(s) = state.buy_robot(Ore, costs) {
        output.push(s);
    }
    state.appreciate();
    output.push(state);
    output
}

/// Returns `true` iff `state` is dominated by another state.
#[allow(unused)]
fn is_dominated(state: &State, others: &[State]) -> bool {
    others
        .iter()
        .any(|other| other.dominates(state) && other != state)
}

/// Returns only those states which are not dominated by any other state in the list.
#[allow(unused)]
fn prune(states: &[State]) -> Vec<State> {
    states
        .iter()
        .filter(|state| !is_dominated(state, states))
        .copied()
        .collect()
}

/// Returns only those states which are not dominated by another state.
///
/// This function requires the states to be sorted first.
#[allow(unused)]
fn prune_sorted(states: &[State]) -> Vec<State> {
    let mut pruned = Vec::new();
    for state in states.iter() {
        let ok = pruned.iter().all(|p: &State| !p.dominates(state));
        if ok {
            pruned.push(*state);
        }
    }
    pruned
}

/// Returns the optimal state containing the most geodes after the given time limit.
#[must_use]
pub fn optimize_breadth_first(
    blueprint: &Blueprint,
    time_limit: usize,
    stack_size: usize,
) -> Option<State> {
    let mut states = vec![State::default()];
    for _ in 1..=time_limit {
        let next_states: Vec<_> = states
            .into_iter()
            .flat_map(|state| advance(state, &blueprint.costs).into_iter())
            .collect();
        states = next_states;
        states.par_sort_by(|a, b| a.cmp(b).reverse());
        states = states.into_iter().take(stack_size).collect();
    }
    states
        .into_iter()
        .max_by_key(|state| state.num_resource(ResourceKind::Geode))
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_optimize_geodes() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let blueprints = parse_input(&input)?;
        let geodes = blueprints[0].optimize_geodes(24);
        assert_eq!(geodes, 9);
        let geodes = blueprints[1].optimize_geodes(24);
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
        let input = fs::read_to_string("data/example")?;
        let blueprints = parse_input(&input)?;
        let quality_sum = solve_part2(&blueprints);
        assert_eq!(quality_sum, 3348);
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let blueprints = parse_input(&input)?;
        let quality_sum = solve_part2(&blueprints);
        assert_eq!(quality_sum, 37191);
        Ok(())
    }
}
