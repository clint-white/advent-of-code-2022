//! Solutions to [Advent of Code 2022 Day 16](https://adventofcode.com/2022/day/16).

use std::cmp::Reverse;
use std::collections::HashMap;
use std::io;
use std::num::ParseIntError;
use std::ops::{Index, IndexMut};
use std::str::FromStr;

use once_cell::sync::OnceCell;
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

    /// An error parsing an integer
    #[error("Error parsing integer")]
    ParseInt(#[from] ParseIntError),

    /// Error parsing valve report
    #[error("Parse error: '{0}'")]
    ParseValveReport(String),
}

/// A specialized [`Result`] type for operations in this crate.
///
/// [`Result`]: std::result::Result
pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Clone)]
pub struct ValveReport {
    name: String,
    flow_rate: u64,
    tunnels: Vec<String>,
}

impl FromStr for ValveReport {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        // We *could* be more careful with the pluralization of "tunnel", "lead", "valves" making
        // sure that they all agree and agree with whether there are one or more than one valve
        // listed.  But we are not going to bother checking grammar!
        let re = regex!(
            r"Valve (?P<valve>[[:upper:]]+) has flow rate=(?P<rate>\d+); tunnels? leads? to valves? (?P<tunnels>[[:upper:]]+(,\s*[[:upper:]]+)*)"
        );
        let captures = re
            .captures(s)
            .ok_or_else(|| Error::ParseValveReport(s.into()))?;
        let name = captures["valve"].into();
        let flow_rate = captures["rate"].parse()?;
        let sep = regex!(r",\s*");
        let tunnels = sep.split(&captures["tunnels"]).map(String::from).collect();
        let report = Self {
            name,
            flow_rate,
            tunnels,
        };
        Ok(report)
    }
}

pub fn parse_input(s: &str) -> Result<Vec<ValveReport>> {
    s.lines().map(str::parse).collect()
}

#[derive(Debug, Clone)]
pub struct Graph {
    names: Vec<String>,
    indices: HashMap<String, usize>,
    flow_rates: Vec<u64>,
    neighbors: Vec<Vec<usize>>,
}

impl Graph {
    #[must_use]
    pub fn num_nodes(&self) -> usize {
        self.names.len()
    }

    /// Returns the flow rate of the given valve node.
    ///
    /// # Panics
    ///
    /// Panics if `node` is not a valid valve node index.
    #[must_use]
    pub fn flow_rate(&self, node: usize) -> u64 {
        self.flow_rates[node]
    }

    #[must_use]
    pub fn neighbors(&self, node: usize) -> &[usize] {
        self.neighbors[node].as_ref()
    }

    /// Returns a matrix of all pairwise distances between nodes in the graph.
    ///
    /// Uses `usize::MAX` to represent unreachable nodes.
    #[must_use]
    pub fn distances(&self) -> Vec<Vec<u64>> {
        floyd_warshall(&self.neighbors)
    }

    /// Returns the indices of the valves with positive flow rate.
    pub fn find_positive_flow_rates(&self) -> Vec<usize> {
        self.flow_rates
            .iter()
            .enumerate()
            .filter_map(|(index, &rate)| if rate > 0 { Some(index) } else { None })
            .collect()
    }
}

fn floyd_warshall(neighbors: &[Vec<usize>]) -> Vec<Vec<u64>> {
    let n = neighbors.len();
    let mut dist = vec![vec![u64::MAX; n]; n];
    // The diagonal entries are all 0.
    for (i, row) in dist.iter_mut().enumerate() {
        row[i] = 0;
    }
    // The distance between adjacent nodes is 1.
    for (i, row) in neighbors.iter().enumerate() {
        for &j in row {
            dist[i][j] = 1;
        }
    }
    // The `k`th iteration updates the distances between nodes `i` and `j` using the shortest path
    // found so far with intermediate nodes in the set `{0,...,k}`.
    for k in 0..n {
        for i in 0..n {
            for j in 0..n {
                let (ans, overflow) = dist[i][k].overflowing_add(dist[k][j]);
                if !overflow && ans < dist[i][j] {
                    dist[i][j] = ans;
                }
            }
        }
    }
    dist
}

#[must_use]
pub fn compile_graph(reports: &[ValveReport]) -> CompiledGraph {
    let names: Vec<_> = reports
        .iter()
        .map(|report| String::from(&report.name))
        .collect();
    let indices: HashMap<_, _> = names
        .iter()
        .enumerate()
        .map(|(i, name)| (String::from(name), i))
        .collect();
    let flow_rates: Vec<_> = reports.iter().map(|report| report.flow_rate).collect();
    let neighbors: Vec<_> = reports
        .iter()
        .map(|report| report.tunnels.iter().map(|name| indices[name]).collect())
        .collect();

    let graph = Graph {
        names,
        indices,
        flow_rates,
        neighbors,
    };
    CompiledGraph::new(graph)
}

#[derive(Debug, Clone)]
pub struct CompiledGraph {
    graph: Graph,
    targets: Vec<usize>,
    distances: Vec<Vec<u64>>,
    /// The minimum *positive* distance between a pair of target nodes.
    min_distance: u64,
}

impl CompiledGraph {
    pub fn new(graph: Graph) -> Self {
        let targets = graph.find_positive_flow_rates();
        let distances = graph.distances();
        let min_distance = targets
            .iter()
            .flat_map(|i| targets.iter().map(|j| distances[*i][*j]))
            .filter(|&d| d > 0)
            .min()
            .unwrap_or_default();
        Self {
            graph,
            targets,
            distances,
            min_distance,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Optimizer<'a> {
    graph: &'a CompiledGraph,
}

impl<'a> Optimizer<'a> {
    pub fn new(graph: &'a CompiledGraph) -> Self {
        Self { graph }
    }

    pub fn backtrack(&self, start: &str, timeout: u64) -> u64 {
        let lower_bound = self.beam_search(start, timeout, 100);
        let state = State::new(self.graph.graph.indices[start], timeout);
        self.backtrack_inner(state, lower_bound)
    }

    fn backtrack_inner(&self, state: State, lower_bound: u64) -> u64 {
        if state.time_remaining == 0 || self.pressure_bound(&state) < lower_bound {
            return state.pressure;
        }

        self.children(state)
            .map(|child| self.backtrack_inner(child, lower_bound))
            .max()
            .unwrap_or(state.pressure)
    }

    /// Performs a beam search with given beam width and returns the best solution.
    ///
    /// Extends every partial solution in every possible way, and keeps the best `width` of the
    /// extended solutions.
    pub fn beam_search(&self, start: &str, timeout: u64, width: usize) -> u64 {
        let mut beam = vec![State::new(self.graph.graph.indices[start], timeout)];
        let mut finished = vec![];
        for _ in 0..timeout {
            let mut next_generation = Vec::with_capacity(beam.capacity());
            for state in beam {
                if self.is_done(&state) {
                    finished.push(state.pressure);
                } else {
                    next_generation.extend(self.children(state));
                }
            }
            beam = next_generation;
            beam.sort_unstable_by_key(|state| Reverse(state.pressure));
            beam.truncate(width);
        }
        finished.into_iter().max().unwrap_or(0)
    }

    /// Returns an iterator producing children of the given state.
    fn children(&self, state: State) -> impl Iterator<Item = State> + '_ {
        self.graph.targets.iter().filter_map(move |&next_node| {
            let d = self.graph.distances[state.node][next_node];
            if state.is_closed(next_node) && d < state.time_remaining {
                let t = state.time_remaining - d - 1;
                let pressure = t * self.graph.graph.flow_rates[next_node];
                let child = State {
                    pressure: state.pressure + pressure,
                    node: next_node,
                    time_remaining: t,
                    open_valves: state.open_valves | (1 << next_node),
                };
                Some(child)
            } else {
                None
            }
        })
    }

    fn is_done(&self, state: &State) -> bool {
        self.graph.targets.iter().all(|&node| {
            state.is_open(node)
                || self.graph.distances[state.node][node] + 1 >= state.time_remaining
        })
    }

    /// Returns an upper bound on the possible total pressure released by an completion of this
    /// state.
    fn pressure_bound(&self, state: &State) -> u64 {
        if state.time_remaining < self.graph.min_distance + 1 {
            return state.pressure;
        }

        let mut rates: Vec<_> = self
            .graph
            .targets
            .iter()
            .filter_map(|&node| {
                if state.is_closed(node) {
                    Some(self.graph.graph.flow_rates[node])
                } else {
                    None
                }
            })
            .collect();
        rates.sort_unstable();
        state.pressure
            + (0..state.time_remaining - self.graph.min_distance)
                .rev()
                .step_by(1 + self.graph.min_distance as usize)
                .zip(rates.iter().rev())
                .map(|(n, &r)| n * r)
                .sum::<u64>()
    }
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq)]
struct State {
    pressure: u64,
    node: usize,
    time_remaining: u64,
    open_valves: u64,
}

impl State {
    fn new(start_index: usize, timeout: u64) -> Self {
        Self {
            pressure: 0,
            node: start_index,
            time_remaining: timeout,
            open_valves: 0,
        }
    }

    #[inline]
    fn is_closed(&self, valve_index: usize) -> bool {
        self.open_valves & (1 << valve_index) == 0
    }

    #[inline]
    fn is_open(&self, valve_index: usize) -> bool {
        !self.is_closed(valve_index)
    }
}

#[must_use]
pub fn solve_part1(graph: &CompiledGraph) -> u64 {
    let optimizer = Optimizer::new(graph);
    optimizer.backtrack("AA", 30)
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Player {
    One,
    Two,
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq)]
struct Walk {
    /// The destination node of the walk.
    dest: usize,
    /// The time remaining to reach the destination *and* open its valve.
    time: u64,
}

impl Walk {
    /// Decrements the `time` counter if it is positive and returns `true`, otherwise returns
    /// `false`.
    fn step(&mut self) -> bool {
        let (t, overflow) = self.time.overflowing_sub(1);
        if !overflow {
            self.time = t;
        }
        !overflow
    }
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq)]
struct TandemState {
    pressure: u64,
    open_valves: u64,
    player1: Option<Walk>,
    player2: Option<Walk>,
}

impl TandemState {
    fn new(start_index: usize) -> Self {
        Self {
            pressure: 0,
            open_valves: 0,
            player1: Some(Walk {
                dest: start_index,
                time: 0,
            }),
            player2: Some(Walk {
                dest: start_index,
                time: 0,
            }),
        }
    }

    fn pending_times(&self) -> (Option<u64>, Option<u64>) {
        (
            self.player1.map(|walk| walk.time),
            self.player2.map(|walk| walk.time),
        )
    }

    #[inline]
    fn pressure(&self) -> u64 {
        self.pressure
    }

    #[inline]
    fn is_closed_valve(&self, valve_index: usize) -> bool {
        self.open_valves & (1 << valve_index) == 0
    }

    fn step(&mut self) -> (bool, bool) {
        let left = self.player1.map(|mut walk| walk.step()).unwrap_or(true);
        let right = self.player2.map(|mut walk| walk.step()).unwrap_or(true);
        (left, right)
    }

    fn get_mut(&mut self, player: Player) -> Option<&mut Walk> {
        match player {
            Player::One => self.player1.as_mut(),
            Player::Two => self.player2.as_mut(),
        }
    }
}

impl Index<Player> for TandemState {
    type Output = Option<Walk>;

    fn index(&self, player: Player) -> &Self::Output {
        match player {
            Player::One => &self.player1,
            Player::Two => &self.player2,
        }
    }
}

impl IndexMut<Player> for TandemState {
    fn index_mut(&mut self, player: Player) -> &mut Self::Output {
        match player {
            Player::One => &mut self.player1,
            Player::Two => &mut self.player2,
        }
    }
}

#[derive(Debug, Clone)]
pub struct TandemOptimizer<'a> {
    graph: &'a CompiledGraph,
}

impl<'a> TandemOptimizer<'a> {
    pub fn new(graph: &'a CompiledGraph) -> Self {
        Self { graph }
    }

    pub fn beam_search(&self, start: &str, timeout: u64, width: usize) -> u64 {
        let mut beam = vec![TandemState::new(self.graph.graph.indices[start])];
        for remaining in (0..timeout).rev() {
            beam = beam
                .into_iter()
                .flat_map(|state| self.children(state, remaining).into_iter())
                .collect();
            if remaining > 0 {
                beam.sort_unstable_by(|a, b| a.pressure().cmp(&b.pressure()).reverse());
                beam.truncate(width);
            }
        }
        beam.into_iter()
            .map(|state| state.pressure())
            .max()
            .unwrap_or_default()
    }

    pub fn backtrack(&self, start: &str, timeout: u64) -> u64 {
        let lower_bound = self.beam_search(start, timeout, 200);
        let state = TandemState::new(self.graph.graph.indices[start]);
        self.backtrack_inner(state, lower_bound, timeout)
    }

    fn backtrack_inner(&self, state: TandemState, lower_bound: u64, remaining: u64) -> u64 {
        if remaining == 0 || self.pressure_bound(&state, remaining) < lower_bound {
            return state.pressure();
        }

        let children = self.children(state, remaining - 1);
        children
            .into_iter()
            .map(|child| self.backtrack_inner(child, lower_bound, remaining - 1))
            .max()
            .unwrap_or(state.pressure())
    }

    fn children(&self, mut state: TandemState, remaining: u64) -> Vec<TandemState> {
        // Step 1: If either player has pending time 0, choose a new destination node for them and
        // set the pending time to its distance from the current node + 1.
        let mut children = match state.pending_times() {
            (Some(0), Some(0)) => self.advance_both(state, remaining),
            (Some(0), _) => self.advance_single(state, remaining, Player::One),
            (_, Some(0)) => self.advance_single(state, remaining, Player::Two),
            _ => {
                let _ = state.step();
                vec![state]
            }
        };
        // Step 2: Decrement each player's pending times.  If a timer reaches 0, then adjust the
        // state's `pressure` field by the flow rate of the destination node for that player times
        // the remaining time.
        children.iter_mut().for_each(|state| {
            for player in [Player::One, Player::Two] {
                if let Some(walk) = state.get_mut(player) {
                    walk.time -= 1;
                    if walk.time == 0 {
                        state.pressure += remaining * self.graph.graph.flow_rates[walk.dest];
                    }
                }
            }
        });
        children
    }

    fn advance_both(&self, state: TandemState, remaining: u64) -> Vec<TandemState> {
        let v1 = self.advance_single(state, remaining, Player::One);
        let children = v1
            .into_iter()
            .flat_map(|s| self.advance_single(s, remaining, Player::Two));

        if matches!((state.player1, state.player2), (Some(w1), Some(w2)) if w1 == w2) {
            // Break symmetry between player 1 and player 2. This can only happen at the very
            // start, after that the two players will always have different destination nodes.
            children
                .filter(|s| match (s.player1, s.player2) {
                    (Some(w1), Some(w2)) => w1.dest < w2.dest,
                    _ => true,
                })
                .collect()
        } else {
            children.collect()
        }
    }

    fn advance_single(
        &self,
        mut state: TandemState,
        remaining: u64,
        player: Player,
    ) -> Vec<TandemState> {
        let mut children: Vec<_> = self
            .graph
            .targets
            .iter()
            .filter_map(move |&next_node| {
                let d = self.graph.distances[state[player].unwrap().dest][next_node];
                if state.is_closed_valve(next_node) && d + 1 < remaining {
                    let mut child = state;
                    child.open_valves |= 1 << next_node;
                    child[player] = Some(Walk {
                        dest: next_node,
                        time: d + 1,
                    });
                    Some(child)
                } else {
                    None
                }
            })
            .collect();
        // Add the state with this player turned off for the future.
        state[player] = None;
        children.push(state);
        children
    }

    fn pressure_bound(&self, state: &TandemState, time: u64) -> u64 {
        let mut total = state.pressure;

        // Compute the maximum flow rate among the closed valves.
        let max_rate = self
            .graph
            .targets
            .iter()
            .filter_map(|&node| {
                if state.is_closed_valve(node) {
                    Some(self.graph.graph.flow_rates[node])
                } else {
                    None
                }
            })
            .max()
            .unwrap_or(0);
        for player in [Player::One, Player::Two] {
            if let Some(walk) = state[player] {
                // Add in the flow from the pending node.
                total += self.graph.graph.flow_rates[walk.dest] * (time - walk.time);

                // Overestimate future flows: We assume we can open as many of the remaining closed
                // valves as time permits, regardless of what the other player might do.  We find
                // the maximum flow rate among currently closed valves, and assume *all* closed
                // valves have that flow rate.  We assume the distance between any two nodes is the
                // graph's minimum distance.

                // remaining time after opening pending node's valve
                let remaining = time - walk.time;
                // time delta between opening valves
                let delta = 1 + self.graph.min_distance;
                // the number of valves we can open
                let num_valves = remaining / delta;
                // The sum of the remaining times for each of the valves we can open.  We open
                // valves at times `remaining`, `remaining - delta`, `remaining - 2 * delta`, ...
                // The number of terms in the sum is `remaining / delta`.
                let sum_times = remaining * num_valves - delta * num_valves * (num_valves + 1) / 2;
                // The future flow rate this player could release is overestimated as the sum of
                // the remaining times when valves are opened and the maximum flow rate of the
                // currently closed valves.
                total += sum_times * max_rate;
            }
        }

        total
    }
}

#[must_use]
pub fn solve_part2(graph: &CompiledGraph) -> u64 {
    let optimizer = TandemOptimizer::new(graph);
    optimizer.backtrack("AA", 26)
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_part1_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let reports = parse_input(&input)?;
        let graph = compile_graph(&reports);
        let score = solve_part1(&graph);
        assert_eq!(score, 1651);
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let reports = parse_input(&input)?;
        let graph = compile_graph(&reports);
        let score = solve_part1(&graph);
        assert_eq!(score, 2181);
        Ok(())
    }

    #[test]
    fn test_part2_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let reports = parse_input(&input)?;
        let graph = compile_graph(&reports);
        let score = solve_part2(&graph);
        assert_eq!(score, 1707);
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let reports = parse_input(&input)?;
        let graph = compile_graph(&reports);
        let score = solve_part2(&graph);
        assert_eq!(score, 2824);
        Ok(())
    }
}
