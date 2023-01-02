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
        optimize_geodes(&self.costs, time_limit).map_or(0, |state| state.geodes())
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
        write!(f, "State {{ resources=[ ")?;
        for n in self.resources.iter() {
            write!(f, "{n} ")?;
        }
        write!(f, "], robots=[ ")?;
        for n in self.robots.iter() {
            write!(f, "{n} ")?;
        }
        write!(f, "] }}")
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
                // minute by each of the existing robots.  Use `self.robots` when updating
                // resources and not `robots`, as the new robot does not produce any resources
                // during the first minute.
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

    /// Returns an array indicating which robots are affordable.
    fn affordable_robots(&self, costs: &ResourceMatrix<usize>) -> ResourceArray<bool> {
        let mut affordable = ResourceArray::default();
        for i in 0..4 {
            affordable.0[i] = costs.0[i]
                .iter()
                .zip(self.resources.iter())
                .all(|(a, b)| a <= b);
        }
        affordable
    }

    /// Returns an array indicating which robots we will eventually be able to afford given what
    /// robots we currently have.
    fn eventually_affordable_robots(&self, costs: &ResourceMatrix<usize>) -> ResourceArray<bool> {
        let mut eventually_affordable = ResourceArray::default();
        for i in 0..4 {
            eventually_affordable.0[i] = costs.0[i]
                .iter()
                .zip(self.robots.iter())
                .all(|(&c, &r)| c == 0 || r > 0);
        }
        eventually_affordable
    }

    /// Advances a state by one unit of time.
    ///
    /// Returns all possible future states at one time unit later.  The array `limits` are upper
    /// bounds on the number of robots of a given kind which a state can own.  Once such a limit
    /// is reached, advancing the state will no longer include purchasing additional robots of that
    /// kind even one is affordable.
    fn advance(
        mut self,
        costs: &ResourceMatrix<usize>,
        limits: &ResourceArray<usize>,
    ) -> Vec<State> {
        use ResourceKind::{Clay, Geode, Obsidian, Ore};

        let mut descendants = Vec::new();

        if let Some(s) = self.buy_robot(Geode, costs) {
            descendants.push(s);
        }

        if self.robots[Obsidian] < limits[Obsidian] {
            if let Some(s) = self.buy_robot(Obsidian, costs) {
                descendants.push(s);
            }
        }

        if self.robots[Clay] < limits[Clay] {
            if let Some(s) = self.buy_robot(Clay, costs) {
                descendants.push(s);
            }
        }

        if self.robots[Ore] < limits[Ore] {
            if let Some(s) = self.buy_robot(Ore, costs) {
                descendants.push(s);
            }
        }

        // If there is a robot that we cannot currently afford, but which we will be able to afford
        // later if we just wait long enough, then we can purchase nothing at this step.  On the
        // other hand, if we do not have sufficient robots to be able to eventually afford
        // something that we cannot afford now, then we must purchase one of the robots we can
        // afford --- purchasing a robot later instead of now when we can afford it now means we
        // just get less return on it.
        if self
            .eventually_affordable_robots(costs)
            .iter()
            .zip(self.affordable_robots(costs).iter())
            .any(|(&future, now)| future && !now)
        {
            self.appreciate();
            descendants.push(self);
        }
        descendants
    }

    /// Returns a very rough upper bound on the number of geodes that could be produced from this
    /// state with the given amount of time.
    ///
    /// This function blatantly assumes that we will be able to purchase one new geode robot every
    /// minute for the remaining time, whether or not this is possible given the current resources
    /// and robots.
    ///
    /// This is a very fast but poor estimate of the number of geodes that could be produced, but
    /// if the remaining time is somewhat small and the state is suboptimal, it is often sufficient
    /// to rule out this state as being optimal.  It can be used to limit the number of possible
    /// states that need to be considered when performing an exhaustive tree search for the optimal
    /// strategy, if at least one good solution is known.
    #[must_use]
    pub fn bound_geodes(&self, time: usize) -> usize {
        use ResourceKind::Geode;

        self.resources[Geode] + time * self.robots[Geode] + time * time.saturating_sub(1) / 2
    }
}

/// Returns the optimal state containing the most geodes after the given time limit.
pub fn optimize_geodes(costs: &ResourceMatrix<usize>, time_limit: usize) -> Option<State> {
    // Quickly find a good solution and use the number of geodes it provides to further prune the
    // search tree.
    let num_geodes = beam_search(costs, time_limit, 100).map_or(0, |state| state.geodes());

    let robot_limits = maximum_resource_costs(costs);
    let mut states = vec![State::default()];
    for remaining in (0..time_limit).rev() {
        states = states
            .into_iter()
            .flat_map(|state| state.advance(costs, &robot_limits).into_iter())
            .filter(|state| state.bound_geodes(remaining) >= num_geodes)
            .collect();
        if remaining > 0 {
            states.par_sort_by(|a, b| a.cmp(b).reverse());
            states.dedup_by(|a, b| b.dominates(a));
        }
    }
    states.into_iter().max_by_key(State::geodes)
}

pub fn beam_search(
    costs: &ResourceMatrix<usize>,
    time_limit: usize,
    width: usize,
) -> Option<State> {
    let robot_limits = maximum_resource_costs(costs);
    let mut states = vec![State::default()];
    for remaining in (0..time_limit).rev() {
        states = states
            .into_iter()
            .flat_map(|state| state.advance(costs, &robot_limits).into_iter())
            .collect();
        if remaining > 0 {
            states.par_sort_by(|a, b| a.cmp(b).reverse());
            states.dedup_by(|a, b| b.dominates(a));
            states.truncate(width);
        }
    }
    states.into_iter().max_by_key(State::geodes)
}

/// Returns the maximum cost, in terms of each non-terminal resource, of any of the robot kinds.
fn maximum_resource_costs(costs: &ResourceMatrix<usize>) -> ResourceArray<usize> {
    use ResourceKind::{Clay, Geode, Obsidian, Ore};

    let mut max_costs = ResourceArray::default();
    for resource in [Ore, Clay, Obsidian, Geode] {
        max_costs[resource] = [Ore, Clay, Obsidian, Geode]
            .into_iter()
            .map(|robot| costs[robot][resource])
            .max()
            .unwrap();
    }
    max_costs
}

/// Returns the sum of the quality levels of the blueprints in 24 minutes.
#[must_use]
pub fn solve_part1(blueprints: &[Blueprint]) -> usize {
    blueprints
        .par_iter()
        .map(|blueprint| blueprint.quality_level(24))
        .sum()
}

/// Returns the product of the maximum number of geodes possible from each of the first three
/// blueprints in 32 minutes.
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
        assert_eq!(quality_sum, 3472);
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
