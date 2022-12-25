use std::collections::HashMap;
use std::hash::Hash;
use std::ops::{Index, IndexMut};

use crate::{CellKind, Error, Grid, Heading, Instruction, Position, Result};

/// An array of the positions of a cell's neighbors in each of four directions.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Neighbors([Option<State>; 4]);

/// The position and heading on the board.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
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

impl Index<Heading> for Neighbors {
    type Output = Option<State>;

    fn index(&self, heading: Heading) -> &Self::Output {
        self.0.index(heading as usize)
    }
}

impl IndexMut<Heading> for Neighbors {
    fn index_mut(&mut self, heading: Heading) -> &mut Self::Output {
        self.0.index_mut(heading as usize)
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
    pub fn neighbor(&self, state: State) -> Option<State> {
        self.edges[&state.position][state.heading]
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
                    if let Some(s) = graph.neighbor(state) {
                        state = s;
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
    let edges = build_easy_edges(grid);
    let start_col = (1..grid.num_cols() - 1)
        .find(|&j| matches!(grid[[1, j]], Some(CellKind::OpenTile)))
        .ok_or(Error::MissingSource)?;
    let source = State {
        position: [1, start_col],
        heading: Heading::Right,
    };

    let graph = Graph { edges, source };
    Ok(graph)
}

// Initialize the graph using edges that come from adjacent open tiles.  Later we will glue
// along the paired edges when folding the cube, which adds more edges.
fn build_easy_edges(grid: &Grid<Option<CellKind>>) -> HashMap<Position, Neighbors> {
    use Heading::{Down, Left, Right, Up};

    let mut edges = HashMap::new();
    for i in 1..grid.num_rows() - 1 {
        for j in 1..grid.num_cols() - 1 {
            let pos = [i, j];
            if let Some(CellKind::OpenTile) = grid[pos] {
                let mut neighbors = Neighbors::default();
                if let Some(CellKind::OpenTile) = grid[[i, j + 1]] {
                    neighbors[Right] = Some(State {
                        position: [i, j + 1],
                        heading: Right,
                    });
                }
                if let Some(CellKind::OpenTile) = grid[[i, j - 1]] {
                    neighbors[Left] = Some(State {
                        position: [i, j - 1],
                        heading: Left,
                    });
                }
                if let Some(CellKind::OpenTile) = grid[[i + 1, j]] {
                    neighbors[Down] = Some(State {
                        position: [i + 1, j],
                        heading: Down,
                    });
                }
                if let Some(CellKind::OpenTile) = grid[[i - 1, j]] {
                    neighbors[Up] = Some(State {
                        position: [i - 1, j],
                        heading: Up,
                    });
                }
                edges.insert(pos, neighbors);
            }
        }
    }
    edges
}

pub fn glue_edges_example(graph: &mut Graph, grid: &Grid<Option<CellKind>>) {
    use Heading::{Down, Left, Right, Up};

    assert_eq!(grid.num_rows(), 14);
    assert_eq!(grid.num_cols(), 18);
    glue_edges(
        graph,
        grid,
        (5..9).map(|j| [5, j]),
        Up,
        (1..5).map(|i| [i, 9]),
        Right,
    );
    glue_edges(
        graph,
        grid,
        (1..5).map(|j| [5, j]),
        Up,
        (9..13).rev().map(|j| [1, j]),
        Down,
    );
    glue_edges(
        graph,
        grid,
        (5..9).map(|i| [i, 12]),
        Right,
        (13..17).rev().map(|j| [9, j]),
        Down,
    );
    glue_edges(
        graph,
        grid,
        (1..5).map(|i| [i, 12]),
        Right,
        (9..13).rev().map(|i| [i, 16]),
        Left,
    );
    glue_edges(
        graph,
        grid,
        (5..9).map(|j| [8, j]),
        Down,
        (9..13).rev().map(|i| [i, 9]),
        Right,
    );
    glue_edges(
        graph,
        grid,
        (1..5).map(|j| [8, j]),
        Down,
        (9..13).rev().map(|j| [12, j]),
        Up,
    );
    glue_edges(
        graph,
        grid,
        (5..9).map(|i| [i, 1]),
        Left,
        (13..17).rev().map(|j| [12, j]),
        Up,
    );
}

pub fn glue_edges_input(graph: &mut Graph, grid: &Grid<Option<CellKind>>) {
    use Heading::{Down, Left, Right, Up};

    assert_eq!(grid.num_rows(), 202);
    assert_eq!(grid.num_cols(), 152);
    // A
    glue_edges(
        graph,
        grid,
        (1..51).map(|j| [101, j]),
        Up,
        (51..101).map(|i| [i, 51]),
        Right,
    );
    // B
    glue_edges(
        graph,
        grid,
        (151..201).map(|i| [i, 50]),
        Right,
        (51..101).map(|j| [150, j]),
        Up,
    );
    // C
    glue_edges(
        graph,
        grid,
        (51..101).map(|i| [i, 100]),
        Right,
        (101..151).map(|j| [50, j]),
        Up,
    );
    // D
    glue_edges(
        graph,
        grid,
        (101..151).map(|i| [i, 1]),
        Left,
        (1..51).rev().map(|i| [i, 51]),
        Right,
    );
    // E
    glue_edges(
        graph,
        grid,
        (151..201).map(|i| [i, 1]),
        Left,
        (51..101).map(|j| [1, j]),
        Down,
    );
    // F
    glue_edges(
        graph,
        grid,
        (101..151).map(|i| [i, 100]),
        Right,
        (1..51).rev().map(|i| [i, 150]),
        Left,
    );
    // G
    glue_edges(
        graph,
        grid,
        (1..51).map(|j| [200, j]),
        Down,
        (101..151).map(|j| [1, j]),
        Down,
    );
}

fn glue_edges<E1, E2>(
    graph: &mut Graph,
    grid: &Grid<Option<CellKind>>,
    edge1: E1,
    heading1: Heading,
    edge2: E2,
    heading2: Heading,
) where
    E1: IntoIterator<Item = Position>,
    E2: IntoIterator<Item = Position>,
{
    use CellKind::OpenTile;

    for (p1, p2) in edge1.into_iter().zip(edge2.into_iter()) {
        if matches!(grid[p1], Some(OpenTile)) && matches!(grid[p2], Some(OpenTile)) {
            let cell = graph
                .edges
                .get_mut(&p1)
                .expect("open tiles are in the graph");
            cell[heading1] = Some(State {
                position: p2,
                heading: heading2,
            });
            let cell = graph
                .edges
                .get_mut(&p2)
                .expect("open tiles are in the graph");
            cell[heading2.reverse()] = Some(State {
                position: p1,
                heading: heading1.reverse(),
            });
        }
    }
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
        let mut graph = build_graph(&grid)?;
        glue_edges_example(&mut graph, &grid);
        let password = solve(&graph, &instructions);
        assert_eq!(password, 5031);
        Ok(())
    }

    #[test]
    fn test_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let (grid, instructions) = parse_input(&input)?;
        let mut graph = build_graph(&grid)?;
        glue_edges_input(&mut graph, &grid);
        let password = solve(&graph, &instructions);
        assert_eq!(password, 123149);
        Ok(())
    }
}
