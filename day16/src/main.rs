//! Advent of Code 2022 Day 16

use std::io;

use day16::*;

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let reports = parse_input(&input)?;
    let graph = build_graph(&reports);
    let score = solve_part1(&graph);
    println!("[Part 1] Best strategy releases {score} pressure");

    Ok(())
}
