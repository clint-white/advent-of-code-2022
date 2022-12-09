//! Advent of Code 2022 Day 9

use std::io;

use day09::{parse_input, solve_part1, solve_part2, Result};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let motions = parse_input(&input)?;
    let num_positions = solve_part1(&motions);
    println!("[Part 1] The number of unique positions of the tail of the rope: {num_positions}");

    let num_positions = solve_part2(&motions);
    println!("[Part 2] The number of unique positions of the tail of the rope: {num_positions}");

    Ok(())
}
