//! Solutions to [Advent of Code 2022 Day 16](https://adventofcode.com/2022/day/16).

use std::cmp::Reverse;
use std::collections::HashMap;
use std::io;
use std::num::ParseIntError;
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
}

#[must_use]
pub fn build_graph(reports: &[ValveReport]) -> Graph {
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

    Graph {
        names,
        indices,
        flow_rates,
        neighbors,
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ValveState {
    Closed,
    Open,
}

impl ValveState {
    pub fn toggle(&mut self) {
        *self = match self {
            ValveState::Open => ValveState::Closed,
            ValveState::Closed => ValveState::Open,
        }
    }

    #[must_use]
    pub fn is_open(&self) -> bool {
        match self {
            ValveState::Open => true,
            ValveState::Closed => false,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Step {
    OpenValve,
    Move(usize, usize),
}

#[derive(Debug, Clone)]
struct Path<'a> {
    timeout: usize,
    steps: Vec<Step>,
    valve_states: Vec<ValveState>,
    score: u64,
    graph: &'a Graph,
    node: usize,
}

impl<'a> Path<'a> {
    #[must_use]
    fn new(graph: &'a Graph, start: &str, timeout: usize) -> Self {
        let steps = Vec::with_capacity(timeout);
        let valve_states = vec![ValveState::Closed; graph.num_nodes()];
        let score = 0;
        Self {
            timeout,
            steps,
            valve_states,
            score,
            graph,
            node: graph.indices[start],
        }
    }

    #[inline]
    fn score(&self) -> u64 {
        self.score
    }

    #[inline]
    fn remaining(&self) -> usize {
        self.timeout - self.steps.len()
    }

    /// Add the given step to the solution.
    fn push(&mut self, step: Step) {
        // XXX verify `self.remaining > 0`
        match step {
            Step::Move(_from, to) => {
                // XXX verify `dest` is a neighbor of `node`
                // XXX verify that self.node is currently `_from`
                self.node = to;
            }
            Step::OpenValve => {
                // XXX verify valve is currently closed
                self.valve_states[self.node] = ValveState::Open;
                self.score += (self.remaining() - 1) as u64 * self.graph.flow_rate(self.node);
            }
        }
        self.steps.push(step);
    }

    /// Pop the previous step.
    fn pop(&mut self) -> Option<Step> {
        let step = self.steps.pop()?;
        match step {
            Step::Move(from, _to) => {
                // verify that self.node is currently _to
                self.node = from;
            }
            Step::OpenValve => {
                // XXX verify valve is currently open
                self.valve_states[self.node] = ValveState::Closed;
                self.score -= (self.remaining() - 1) as u64 * self.graph.flow_rate(self.node);
            }
        }
        Some(step)
    }

    /// Returns a vector of the feasible steps the solution could take next.
    fn feasible_steps(&self) -> Vec<Step> {
        let mut steps = Vec::new();
        if matches!(self.valve_states[self.node], ValveState::Closed)
            && self.graph.flow_rate(self.node) > 0
        {
            steps.push(Step::OpenValve);
        }
        let neighbors = self.graph.neighbors(self.node);
        steps.extend(
            neighbors
                .iter()
                .map(|&neighbor| Step::Move(self.node, neighbor)),
        );
        steps
    }

    /// Returns an upper bound for the final score for the current partial solution.
    ///
    /// Any extension of the current solution will have a score not exceeding this value.
    fn bound_score(&self) -> u64 {
        let mut rates: Vec<_> = self
            .valve_states
            .iter()
            .zip(self.graph.flow_rates.iter())
            .filter_map(|(state, rate)| {
                if matches!(state, ValveState::Closed) {
                    Some(rate)
                } else {
                    None
                }
            })
            .collect();
        rates.sort_unstable();
        self.score
            + (0..self.remaining())
                .rev()
                .step_by(2)
                .zip(rates.iter().rev())
                .map(|(n, &&r)| n as u64 * r)
                .sum::<u64>()
    }
}

/// Find the strategy that releases the most pressure.
///
/// This function uses a combination of a fast, suboptimal beam search and a slower, complete
/// backtracking algorithm to find the optimal solution.  The beam search finds a near-optimal
/// solution very quickly, which allows pruning poor partial solutions earlier in backtrack search
/// than otherwise would be possible.  This leads to a substantial performance improvement.
fn find_optimal_strategy<'a>(graph: &'a Graph, start: &str, timeout: usize) -> Path<'a> {
    // Quickly find a near-optimal solution with a beam search.
    let best = beam_search(graph, start, timeout, 100);
    let path = Path::new(graph, start, timeout);
    // Search under each child of the tree root in its own thread.
    path.feasible_steps()
        .into_par_iter()
        .map(|step| {
            let mut b = best.clone();
            let mut p = path.clone();
            p.push(step);
            search_with_backtrack(&mut p, &mut b);
            b
        })
        .max_by_key(Path::score)
        .unwrap()
}

/// Extends `path` with backtracking, updating the global best solution.
fn search_with_backtrack<'a>(path: &mut Path<'a>, best: &mut Path<'a>) {
    let bound = path.bound_score();
    if bound == path.score() || path.remaining() == 0 {
        if path.score() > best.score() {
            *best = path.clone();
        }
        return;
    }
    if bound <= best.score() {
        return;
    }
    for step in path.feasible_steps() {
        path.push(step);
        search_with_backtrack(path, best);
        path.pop();
    }
}

/// Performs a beam search with given beam width and returns the best solution.
///
/// Extends every partial solution in every possible way, and keeps the best `width` of the
/// extended solutions.
fn beam_search<'a>(graph: &'a Graph, start: &str, timeout: usize, width: usize) -> Path<'a> {
    let mut stack = vec![Path::new(graph, start, timeout)];
    for _ in 0..timeout {
        let mut children = next_generation(&stack);
        children.sort_unstable_by_key(|p| Reverse(p.score()));
        stack = children.into_iter().take(width).collect();
    }
    stack.swap_remove(0)
}

/// Steps a list of partial solutions forward one step and returns a vector of the new solutions.
fn next_generation<'a>(stack: &[Path<'a>]) -> Vec<Path<'a>> {
    let mut children = vec![];
    for path in stack.iter() {
        for step in path.feasible_steps() {
            let mut p = path.clone();
            p.push(step);
            children.push(p);
        }
    }
    children
}

#[must_use]
pub fn solve_part1(graph: &Graph) -> u64 {
    let strategy = find_optimal_strategy(graph, "AA", 30);
    strategy.score
}

#[derive(Debug, Clone)]
struct TandemPath<'a> {
    timeout: usize,
    steps: Vec<(Step, Step)>,
    valve_states: Vec<ValveState>,
    score: u64,
    graph: &'a Graph,
    nodes: (usize, usize),
}

impl<'a> TandemPath<'a> {
    #[must_use]
    fn new(graph: &'a Graph, start: &str, timeout: usize) -> Self {
        let steps = Vec::with_capacity(timeout);
        let valve_states = vec![ValveState::Closed; graph.num_nodes()];
        let score = 0;
        Self {
            timeout,
            steps,
            valve_states,
            score,
            graph,
            nodes: (graph.indices[start], graph.indices[start]),
        }
    }

    #[inline]
    fn score(&self) -> u64 {
        self.score
    }

    #[inline]
    fn remaining(&self) -> usize {
        self.timeout - self.steps.len()
    }

    /// Returns an upper bound for the final score for the current partial solution.
    ///
    /// Any extension of the current solution will have a score not exceeding this value.
    fn bound_score(&self) -> u64 {
        let mut rates: Vec<_> = self
            .valve_states
            .iter()
            .zip(self.graph.flow_rates.iter())
            .filter_map(|(state, rate)| {
                if matches!(state, ValveState::Closed) {
                    Some(rate)
                } else {
                    None
                }
            })
            .collect();
        rates.sort_unstable_by(|a, b| a.cmp(b).reverse());

        self.score
            + (0..self.remaining())
                .rev()
                .step_by(2)
                .zip(rates.chunks(2))
                .map(|(n, rates)| (n as u64) * (*rates[0] + **rates.get(1).unwrap_or(&&0)))
                .sum::<u64>()
    }

    /// Sorts the neighbors of a node in decreasing order of the flow rates of their valves if the
    /// valve is closed.
    ///
    /// If a valve is open, 0 is used instead.
    fn sorted_neighbors(&self, node: usize, exclude: Option<usize>) -> Vec<usize> {
        // Sort the neighbors by flow rate if their valve is closed.  Negate the flow rate so that
        // we reverse the order.
        let mut neighbors = self.graph.neighbors(node).to_vec();
        if let Some(taboo) = exclude {
            let i = neighbors
                .iter()
                .enumerate()
                .find_map(|(i, &n)| if n == taboo { Some(i) } else { None })
                .expect("the graph is undirected");
            neighbors.remove(i);
        }
        neighbors.sort_by_key(|&idx| {
            if matches!(self.valve_states[idx], ValveState::Closed) {
                -(self.graph.flow_rate(idx) as isize)
            } else {
                0
            }
        });
        neighbors
    }

    /// Returns `true` iff the valve at the given node is currently close and has a nonzero flow
    /// rate.
    fn valve_worth_opening(&self, node: usize) -> bool {
        matches!(self.valve_states[node], ValveState::Closed) && self.graph.flow_rate(node) > 0
    }

    fn feasible_step_pairs(&self) -> Vec<(Step, Step)> {
        let (you, elephant) = self.nodes;
        let mut you_exclude = None;
        let mut elephant_exclude = None;
        if let Some((your_last, elephant_last)) = self.steps.last() {
            if let Step::Move(from, _to) = your_last {
                you_exclude = Some(from);
            }
            if let Step::Move(from, _to) = elephant_last {
                elephant_exclude = Some(from);
            }
        }

        let your_neighbors = self.sorted_neighbors(you, you_exclude.copied());
        let elephant_neighbors = self.sorted_neighbors(elephant, elephant_exclude.copied());

        let mut steps = Vec::new();

        if self.valve_worth_opening(you) {
            steps.extend(
                elephant_neighbors
                    .iter()
                    .map(|&dest| (Step::OpenValve, Step::Move(elephant, dest))),
            );
        }

        if self.valve_worth_opening(elephant) {
            steps.extend(
                your_neighbors
                    .iter()
                    .map(|&dest| (Step::Move(you, dest), Step::OpenValve)),
            );
        }

        if you != elephant && self.valve_worth_opening(you) && self.valve_worth_opening(elephant) {
            steps.push((Step::OpenValve, Step::OpenValve));
        }

        if you == elephant {
            for i in 0..your_neighbors.len() {
                for j in i..your_neighbors.len() {
                    steps.push((
                        Step::Move(you, your_neighbors[i]),
                        Step::Move(elephant, your_neighbors[j]),
                    ));
                }
            }
        } else {
            for &n1 in &your_neighbors {
                for &n2 in &elephant_neighbors {
                    steps.push((Step::Move(you, n1), Step::Move(elephant, n2)));
                }
            }
        }
        steps
    }

    /// Add the given pair of steps to the solution.
    fn push_pair(&mut self, you: Step, elephant: Step) {
        // XXX verify `self.remaining > 0`
        match you {
            Step::Move(_from, to) => {
                // XXX verify `dest` is a neighbor of `node`
                // XXX verify that self.node is currently `_from`
                self.nodes.0 = to;
            }
            Step::OpenValve => {
                // XXX verify valve is currently closed
                self.valve_states[self.nodes.0] = ValveState::Open;
                self.score += (self.remaining() - 1) as u64 * self.graph.flow_rate(self.nodes.0);
            }
        }
        match elephant {
            Step::Move(_from, to) => {
                // XXX verify `dest` is a neighbor of `node`
                // XXX verify that self.node is currently `_from`
                self.nodes.1 = to;
            }
            Step::OpenValve => {
                // XXX verify valve is currently closed
                self.valve_states[self.nodes.1] = ValveState::Open;
                self.score += (self.remaining() - 1) as u64 * self.graph.flow_rate(self.nodes.1);
            }
        }
        self.steps.push((you, elephant));
    }

    /// Pop the previous pair of steps.
    fn pop_pair(&mut self) -> Option<(Step, Step)> {
        let (your_step, elephant_step) = self.steps.pop()?;
        match your_step {
            Step::Move(from, _to) => {
                // verify that self.node is currently _to
                self.nodes.0 = from;
            }
            Step::OpenValve => {
                // XXX verify valve is currently open
                self.valve_states[self.nodes.0] = ValveState::Closed;
                self.score -= (self.remaining() - 1) as u64 * self.graph.flow_rate(self.nodes.0);
            }
        }

        match elephant_step {
            Step::Move(from, _to) => {
                // verify that self.node is currently _to
                self.nodes.1 = from;
            }
            Step::OpenValve => {
                // XXX verify valve is currently open
                self.valve_states[self.nodes.1] = ValveState::Closed;
                self.score -= (self.remaining() - 1) as u64 * self.graph.flow_rate(self.nodes.1);
            }
        }
        Some((your_step, elephant_step))
    }
}

fn find_optimal_tandem_strategy<'a>(
    graph: &'a Graph,
    start: &str,
    timeout: usize,
) -> TandemPath<'a> {
    let best = tandem_beam_search(graph, start, timeout, 100);
    let path = TandemPath::new(graph, start, timeout);
    path.feasible_step_pairs()
        .into_par_iter()
        .map(|(you, elephant)| {
            let mut p = path.clone();
            p.push_pair(you, elephant);
            let mut b = best.clone();
            search_tandem_with_backtracking(&mut p, &mut b);
            b
        })
        .max_by_key(TandemPath::score)
        .unwrap()
}

fn search_tandem_with_backtracking<'a>(path: &mut TandemPath<'a>, best: &mut TandemPath<'a>) {
    let bound = path.bound_score();
    if bound == path.score() || path.remaining() == 0 {
        if path.score() > best.score() {
            *best = path.clone();
        }
        return;
    }
    if bound <= best.score() {
        return;
    }
    for (you, elephant) in path.feasible_step_pairs() {
        path.push_pair(you, elephant);
        search_tandem_with_backtracking(path, best);
        path.pop_pair();
    }
}

fn tandem_beam_search<'a>(
    graph: &'a Graph,
    start: &str,
    timeout: usize,
    width: usize,
) -> TandemPath<'a> {
    let mut stack = vec![TandemPath::new(graph, start, timeout)];
    for _ in 0..timeout {
        let mut children = next_tandem_generation(&stack);
        children.sort_unstable_by_key(|p| Reverse(p.score()));
        stack = children.into_iter().take(width).collect();
    }
    stack.swap_remove(0)
}

fn next_tandem_generation<'a>(stack: &[TandemPath<'a>]) -> Vec<TandemPath<'a>> {
    let mut children = vec![];
    for path in stack.iter() {
        for (a, b) in path.feasible_step_pairs() {
            let mut p = path.clone();
            p.push_pair(a, b);
            children.push(p);
        }
    }
    children
}

#[must_use]
pub fn solve_part2(graph: &Graph) -> u64 {
    let strategy = find_optimal_tandem_strategy(graph, "AA", 26);
    strategy.score
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_part1_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let reports = parse_input(&input)?;
        let graph = build_graph(&reports);
        let score = solve_part1(&graph);
        assert_eq!(score, 1651);
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let reports = parse_input(&input)?;
        let graph = build_graph(&reports);
        let score = solve_part1(&graph);
        assert_eq!(score, 2181);
        Ok(())
    }

    #[test]
    fn test_part2_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let reports = parse_input(&input)?;
        let graph = build_graph(&reports);
        let score = solve_part2(&graph);
        assert_eq!(score, 1707);
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let reports = parse_input(&input)?;
        let graph = build_graph(&reports);
        let score = solve_part2(&graph);
        assert_eq!(score, 2824);
        Ok(())
    }
}
