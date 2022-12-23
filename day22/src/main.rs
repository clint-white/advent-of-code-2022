//! Advent of Code 2022 Day 22

use std::io;

use day22::{parse_input, part1, Result};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let (grid, instructions) = parse_input(&input)?;
    let graph = part1::build_graph(&grid)?;
    let password = part1::solve(&graph, &instructions);
    println!("[Part 1] The final password is {password}");

    Ok(())
}
