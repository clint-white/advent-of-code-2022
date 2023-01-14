//! Advent of Code 2022 Day 16

use std::io;
use std::time::Instant;

use day16::{compile_graph, parse_input, solve_part1, solve_part2, Result};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let reports = parse_input(&input)?;
    let graph = compile_graph(&reports);

    let mark = Instant::now();
    let score = solve_part1(&graph);
    let elapsed = mark.elapsed();
    println!("[Part 1] Best strategy releases {score} pressure");
    println!("[Part 1] Elapsed time: {elapsed:?}");

    let mark = Instant::now();
    let score = solve_part2(&graph);
    let elapsed = mark.elapsed();
    println!("[Part 2] Best tandem strategy releases {score} pressure");
    println!("[Part 2] Elapsed time: {elapsed:?}");

    Ok(())
}
