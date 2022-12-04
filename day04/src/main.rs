//! Advent of Code 2022 Day 4

use std::io;

use day04::{parse_input, solve_part1, solve_part2, Result};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let ranges = parse_input(&input)?;

    let count = solve_part1(&ranges);
    println!("Number of assignment pairs in which one range fully contains the other: {count}");

    let count = solve_part2(&ranges);
    println!("Number of overlapping assignment pairs: {count}");

    Ok(())
}
