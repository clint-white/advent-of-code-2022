//! Advent of Code 2022 Day 16

use std::io;

use day16::{build_graph, parse_input, solve_part1, solve_part2, Result};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let reports = parse_input(&input)?;
    let graph = build_graph(&reports);
    let score = solve_part1(&graph);
    println!("[Part 1] Best strategy releases {score} pressure");

    let score = solve_part2(&graph);
    println!("[Part 2] Best tandem strategy releases {score} pressure");

    Ok(())
}
