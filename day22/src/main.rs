//! Advent of Code 2022 Day 22

use std::io;

use day22::{build_graph, parse_input, solve_part1, Result};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let (grid, instructions) = parse_input(&input)?;
    let graph = build_graph(&grid)?;
    let password = solve_part1(&graph, &instructions);
    println!("[Part 1] The final password is {password}");

    Ok(())
}
