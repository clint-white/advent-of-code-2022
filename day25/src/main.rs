//! Advent of Code 2022 Day 25

use std::io;

use day25::{parse_input, solve_part1, Result};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let xs = parse_input::<i64>(&input)?;
    let snafu = solve_part1(&xs);
    println!("[Part 1] Sum of input: {snafu}");

    Ok(())
}
