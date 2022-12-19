//! Solutions to [Advent of Code 2022 Day 16](https://adventofcode.com/2022/day/16).

use std::collections::HashMap;
use std::io;
use std::num::ParseIntError;
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

    /// And the given step to the solution.
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
        // Sort the neighbors by flow rate if their valve is closed
        let mut neighbors = self.graph.neighbors(self.node).to_vec();
        neighbors.sort_by_key(|&node| {
            if matches!(self.valve_states[node], ValveState::Closed) {
                self.graph.flow_rate(node)
            } else {
                0
            }
        });
        for neighbor in neighbors.into_iter().rev() {
            steps.push(Step::Move(self.node, neighbor));
        }
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

fn find_optimal_strategy<'a>(graph: &'a Graph, start: &str, timeout: usize) -> Path<'a> {
    let mut best = Path::new(graph, start, timeout);
    let mut path = Path::new(graph, start, timeout);
    extend(&mut path, &mut best);
    best
}

/*
fn extend_loop<'a>(path: &mut Path<'a>, best: &mut Path<'a>) {
    let mut stack = Vec::new();
    stack.push(path.feasible_steps().into_iter());

    loop {
        let bound = path.bound_score();
        if bound == path.score() || path.remaining() == 0 {
            if path.score() > best.score() {
                *best = path.clone();
            }
            path.pop();
            continue;
        }
        if bound <= best.score() {
            path.pop();
            continue;
        }
        let mut steps = path.feasible_steps();
        if let Some(step) = steps.next() {
            stack.push(steps);
        }

    }
}
*/

fn extend<'a>(path: &mut Path<'a>, best: &mut Path<'a>) {
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
        extend(path, best);
        path.pop();
    }
}

#[must_use]
pub fn solve_part1(graph: &Graph) -> u64 {
    let strategy = find_optimal_strategy(graph, "AA", 30);
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
        todo!();
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        todo!();
    }
}
