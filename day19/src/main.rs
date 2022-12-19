//! Advent of Code 2022 Day 19

use std::io;

use day19::{parse_input, solve_part1, Result};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let blueprints = parse_input(&input)?;
    let quality_level_sum = solve_part1(&blueprints);
    println!("[Part 1] Sum of quality levels of blueprints: {quality_level_sum}");

    Ok(())
}
