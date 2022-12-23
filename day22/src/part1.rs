use std::collections::HashMap;
use std::ops::{Index, IndexMut};

use crate::{CellKind, Error, Grid, Heading, Instruction, Position, Result};

/// An array of the positions of a cell's neighbors in each of four directions.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Neighbors([Option<Position>; 4]);

impl Index<Heading> for Neighbors {
    type Output = Option<Position>;

    fn index(&self, heading: Heading) -> &Self::Output {
        self.0.index(heading as usize)
    }
}

impl IndexMut<Heading> for Neighbors {
    fn index_mut(&mut self, heading: Heading) -> &mut Self::Output {
        self.0.index_mut(heading as usize)
    }
}

/// The position and heading on the board.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct State {
    pub position: Position,
    pub heading: Heading,
}

impl State {
    #[must_use]
    pub fn password(&self) -> usize {
        1000 * self.position[0] + 4 * self.position[1] + self.heading.facing()
    }
}

#[derive(Debug, Clone)]
pub struct Graph {
    edges: HashMap<Position, Neighbors>,
    source: State,
}

impl Graph {
    /// Returns the position of the neighbor of a given postion in the given direction.
    #[must_use]
    pub fn neighbor(&self, position: Position, heading: Heading) -> Option<Position> {
        self.edges[&position][heading]
    }

    #[must_use]
    pub fn source(&self) -> State {
        self.source
    }
}

#[must_use]
pub fn solve(graph: &Graph, instructions: &[Instruction]) -> usize {
    let mut state = graph.source();
    for &instruction in instructions {
        match instruction {
            Instruction::Forward(steps) => {
                for _ in 0..steps {
                    if let Some(pos) = graph.neighbor(state.position, state.heading) {
                        state.position = pos;
                    } else {
                        break;
                    }
                }
            }
            Instruction::Rotate(dir) => {
                state.heading.rotate(dir);
            }
        }
    }
    state.password()
}

/// Builds a graph from a grid of cells.
///
/// # Errors
///
/// Returns an error if the implicit source of the graph, i.e., the first open tile on the first
/// row, does not exist.
pub fn build_graph(grid: &Grid<Option<CellKind>>) -> Result<Graph> {
    use CellKind::OpenTile;
    use Heading::{Down, Left, Right, Up};

    // Initialize the graph so that the nodes are the open tiles in the grid and each node has no
    // neighbors at this point.
    let mut edges = HashMap::new();
    for i in 1..grid.num_rows() - 1 {
        for j in 1..grid.num_cols() - 1 {
            let pos = [i, j];
            if let Some(CellKind::OpenTile) = grid[pos] {
                edges.insert(pos, Neighbors::default());
            }
        }
    }

    // Add right and left neighbors.
    for i in 1..grid.num_rows() - 1 {
        // Right neighbors
        // Track the cell an entry in this row would wrap around to.
        let mut wrap_around = None;
        for j in 1..grid.num_cols() - 1 {
            if matches!((grid[[i, j - 1]], grid[[i, j]]), (None, Some(OpenTile))) {
                wrap_around = Some([i, j]);
            }
            match (grid[[i, j]], grid[[i, j + 1]]) {
                (Some(OpenTile), Some(OpenTile)) => {
                    let neighbors = edges.get_mut(&[i, j]).expect("open tiles are in the edges");
                    neighbors[Right] = Some([i, j + 1]);
                }
                (Some(OpenTile), None) => {
                    let neighbors = edges.get_mut(&[i, j]).expect("open tiles are in the edges");
                    neighbors[Right] = wrap_around;
                }
                _ => (),
            }
        }

        // Left neighbors
        let mut wrap_around = None;
        for j in (1..grid.num_cols() - 1).rev() {
            if matches!((grid[[i, j + 1]], grid[[i, j]]), (None, Some(OpenTile))) {
                wrap_around = Some([i, j]);
            }
            match (grid[[i, j]], grid[[i, j - 1]]) {
                (Some(OpenTile), Some(OpenTile)) => {
                    let neighbors = edges.get_mut(&[i, j]).expect("open tiles are in the edges");
                    neighbors[Left] = Some([i, j - 1]);
                }
                (Some(OpenTile), None) => {
                    let neighbors = edges.get_mut(&[i, j]).expect("open tiles are in the edges");
                    neighbors[Left] = wrap_around;
                }
                _ => (),
            }
        }
    }

    // Add down and up neighbors.
    for j in 1..grid.num_cols() - 1 {
        // Down neighbors
        // Track the cell an entry in this row would wrap around to.
        let mut wrap_around = None;
        for i in 1..grid.num_rows() - 1 {
            if matches!((grid[[i - 1, j]], grid[[i, j]]), (None, Some(OpenTile))) {
                wrap_around = Some([i, j]);
            }
            match (grid[[i, j]], grid[[i + 1, j]]) {
                (Some(OpenTile), Some(OpenTile)) => {
                    let neighbors = edges.get_mut(&[i, j]).expect("open tiles are in the edges");
                    neighbors[Down] = Some([i + 1, j]);
                }
                (Some(OpenTile), None) => {
                    let neighbors = edges.get_mut(&[i, j]).expect("open tiles are in the edges");
                    neighbors[Down] = wrap_around;
                }
                _ => (),
            }
        }

        // Up neighbors
        let mut wrap_around = None;
        for i in (1..grid.num_rows() - 1).rev() {
            if matches!((grid[[i + 1, j]], grid[[i, j]]), (None, Some(OpenTile))) {
                wrap_around = Some([i, j]);
            }
            match (grid[[i, j]], grid[[i - 1, j]]) {
                (Some(OpenTile), Some(OpenTile)) => {
                    let neighbors = edges.get_mut(&[i, j]).expect("open tiles are in the edges");
                    neighbors[Up] = Some([i - 1, j]);
                }
                (Some(OpenTile), None) => {
                    let neighbors = edges.get_mut(&[i, j]).expect("open tiles are in the edges");
                    neighbors[Up] = wrap_around;
                }
                _ => (),
            }
        }
    }
    let start_col = (1..grid.num_cols() - 1)
        .find(|&j| matches!(grid[[1, j]], Some(OpenTile)))
        .ok_or(Error::MissingSource)?;
    let source = State {
        position: [1, start_col],
        heading: Right,
    };

    let graph = Graph { edges, source };
    Ok(graph)
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;
    use crate::*;

    #[test]
    fn test_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let (grid, instructions) = parse_input(&input)?;
        let graph = build_graph(&grid)?;
        let password = solve(&graph, &instructions);
        assert_eq!(password, 6032);
        Ok(())
    }

    #[test]
    fn test_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let (grid, instructions) = parse_input(&input)?;
        let graph = build_graph(&grid)?;
        let password = solve(&graph, &instructions);
        assert_eq!(password, 55244);
        Ok(())
    }
}
