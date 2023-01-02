//! Advent of Code 2022 Day 22

use std::io;

use day22::{parse_input, part1, part2, Result};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let (grid, instructions) = parse_input(&input)?;
    let graph = part1::build_graph(&grid)?;
    let password = part1::solve(&graph, &instructions);
    println!("[Part 1] The final password is {password}");

    let mut graph = part2::build_graph(&grid)?;
    // We hardcode edge gluing rules for the puzzle input and the example.  Detect which we were
    // given on stdin by the shape of the grid.
    match grid.shape() {
        [202, 152] => part2::glue_edges_input(&mut graph, &grid),
        [14, 18] => part2::glue_edges_example(&mut graph, &grid),
        _ => {
            let error =
                io::Error::new(io::ErrorKind::InvalidInput, "unrecognized input grid shape");
            return Err(error.into());
        }
    }
    let password = part2::solve(&graph, &instructions);
    println!("[Part 2] The final password is {password}");

    Ok(())
}
