//! Solutions to [Advent of Code 2022 Day 12](https://adventofcode.com/2022/day/12).

use std::io;

pub use ndarray::Array2;
use ndarray::{ShapeError, Zip};
use thiserror::Error;

/// The error type for operations in this crate.
#[derive(Debug, Error)]
pub enum Error {
    /// An underlying [`io::Error`].
    #[error("I/O error")]
    Io(#[from] io::Error),

    /// Illegal byte in input
    #[error("Parse error: '0x{0:02x}'")]
    Parse(u8),

    /// A shape error creating array from input grid.
    #[error("An underlying shape error creating array")]
    Shape(#[from] ShapeError),

    /// The input does not form a grid.
    #[error("The input is not in the shape of a grid")]
    NotGrid,

    /// No source node specified
    #[error("No source node specified")]
    MissingSource,

    /// No sink node specified
    #[error("No sink node specified")]
    MissingSink,

    /// Multiple source nodes
    #[error("More than one source node specified")]
    MultipleSources,

    /// Multiple sink nodes
    #[error("More than one sink node specified")]
    MultipleSinks,
}

/// A specialized [`Result`] type for operations in this crate.
///
/// [`Result`]: std::result::Result
pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Clone)]
pub struct HeightMap {
    array: Array2<u8>,
    source: [usize; 2],
    sink: [usize; 2],
}

impl HeightMap {
    #[inline]
    #[must_use]
    pub fn num_rows(&self) -> usize {
        self.array.shape()[0]
    }

    #[inline]
    #[must_use]
    pub fn num_cols(&self) -> usize {
        self.array.shape()[1]
    }

    #[inline]
    #[must_use]
    pub fn dimensions(&self) -> (usize, usize) {
        let shape = self.array.shape();
        (shape[0], shape[1])
    }

    #[inline]
    #[must_use]
    pub fn source(&self) -> [usize; 2] {
        self.source
    }

    #[inline]
    #[must_use]
    pub fn sink(&self) -> [usize; 2] {
        self.sink
    }

    /// Returns an iterator yielding the neighbors of a given node.
    ///
    /// # Panics
    ///
    /// Panics if the node is out of bounds for the grid.
    pub fn neighbors<'a, F>(
        &'a self,
        node: [usize; 2],
        allowed: F,
    ) -> impl Iterator<Item = [usize; 2]> + '_
    where
        F: Fn([usize; 2], [usize; 2]) -> bool + 'a,
    {
        let i = node[0];
        let j = node[1];
        let (nrows, ncols) = self.dimensions();
        let adjacent = [
            (i.checked_sub(1), Some(j)),
            (if i + 1 < nrows { Some(i + 1) } else { None }, Some(j)),
            (Some(i), j.checked_sub(1)),
            (Some(i), if j + 1 < ncols { Some(j + 1) } else { None }),
        ];
        adjacent.into_iter().filter_map(move |(a, b)| match (a, b) {
            (Some(k), Some(l)) if allowed([i, j], [k, l]) => Some([k, l]),
            _ => None,
        })
    }
}

/// Finds the shortest paths from the source node to every other node.
pub fn find_shortest_paths<'a, F>(
    graph: &'a HeightMap,
    source: [usize; 2],
    allowed: F,
) -> Array2<Option<usize>>
where
    F: Fn([usize; 2], [usize; 2]) -> bool + 'a,
{
    let mut visited: Array2<Option<usize>> = Array2::default(graph.array.raw_dim());
    let mut current_nodes = vec![source];
    visited[source] = Some(0);
    while !current_nodes.is_empty() {
        let mut next_nodes = Vec::new();
        for node in current_nodes {
            let d = visited[node].expect("node has been visited");
            for child in graph.neighbors(node, &allowed) {
                if visited[child].is_none() {
                    visited[child] = Some(d + 1);
                    next_nodes.push(child);
                }
            }
        }
        current_nodes = next_nodes;
    }
    visited
}

#[must_use]
pub fn solve_part1(graph: &HeightMap) -> Option<usize> {
    find_shortest_paths(graph, graph.source, |from, to| {
        graph.array[to] <= graph.array[from] + 1
    })[graph.sink]
}

#[must_use]
pub fn solve_part2(graph: &HeightMap) -> Option<usize> {
    let distances = find_shortest_paths(graph, graph.sink, |from, to| {
        graph.array[from] <= graph.array[to] + 1
    });
    Zip::from(&graph.array)
        .and(distances.view())
        .fold(None, |min, &height, &distance| {
            match (min, height, distance) {
                (None, 0, Some(d)) => Some(d),
                (None, _, _) => None,
                (Some(m), 0, Some(d)) => Some(m.min(d)),
                (Some(m), _, _) => Some(m),
            }
        })
}

/// Parses the problem input into a [`HeightMap`].
///
/// # Errors
///
/// This function returns an error in the following situations:
///
/// 1. If the input map does not form a rectangular grid.
/// 2. If the inputs contains characters other than ascii lowercase or 'S' or 'E'.
/// 3. If there is not exactly one cell containing an 'S'.
/// 4. If there is not exactly one cell containing an 'E'.
pub fn parse_input(s: &str) -> Result<HeightMap> {
    let mut data = Vec::new();
    let mut nrows = 0;
    let mut ncols = None;
    let mut source = None;
    let mut sink = None;
    for line in s.lines() {
        let bytes = line.trim().as_bytes();

        // Make sure the length of this row is consistent with previous rows.
        if let Some(n) = ncols {
            if n != bytes.len() {
                return Err(Error::NotGrid);
            }
        } else {
            ncols = Some(bytes.len());
        }

        // Prepare the row data as `i8`.
        let result: Result<Vec<_>> = bytes
            .iter()
            .map(|byte| match byte {
                b'S' => Ok(0),
                b'E' => Ok(b'z' - b'a'),
                c if c.is_ascii_lowercase() => Ok(c - b'a'),
                c => Err(Error::Parse(*c)),
            })
            .collect();
        let row = result?;
        data.extend(row);

        // Look for source and sink.  Return an error if we find more than one of either.
        let sources = find(bytes, |&c| c == b'S');
        if sources.len() > 1 || (source.is_some() && sources.len() == 1) {
            return Err(Error::MultipleSources);
        }
        if let Some(&col) = sources.first() {
            source = Some([nrows, col]);
        }

        let sinks = find(bytes, |&c| c == b'E');
        if sinks.len() > 1 || (sink.is_some() && sinks.len() == 1) {
            return Err(Error::MultipleSinks);
        }
        if let Some(&col) = sinks.first() {
            sink = Some([nrows, col]);
        }
        nrows += 1;
    }
    let array = Array2::from_shape_vec((nrows, ncols.unwrap_or(0)), data)?;
    let source = source.ok_or(Error::MissingSource)?;
    let sink = sink.ok_or(Error::MissingSink)?;
    let height_map = HeightMap {
        array,
        source,
        sink,
    };
    Ok(height_map)
}

fn find<F>(row: &[u8], pred: F) -> Vec<usize>
where
    F: Fn(&u8) -> bool,
{
    row.iter()
        .enumerate()
        .filter_map(|(i, b)| if pred(b) { Some(i) } else { None })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_part1_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let graph = parse_input(&input)?;
        let shortest_path = solve_part1(&graph);
        assert_eq!(shortest_path, Some(31));
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let graph = parse_input(&input)?;
        let shortest_path = solve_part1(&graph);
        assert_eq!(shortest_path, Some(370));
        Ok(())
    }

    #[test]
    fn test_part2_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let graph = parse_input(&input)?;
        let shortest_path = solve_part2(&graph);
        assert_eq!(shortest_path, Some(29));
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let graph = parse_input(&input)?;
        let shortest_path = solve_part2(&graph);
        assert_eq!(shortest_path, Some(363));
        Ok(())
    }
}
