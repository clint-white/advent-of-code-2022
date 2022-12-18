//! Advent of Code 2022 Day 15

use std::env;
use std::io;

use day15::{parse_input, solve_part1, solve_part2, Result};

fn main() -> Result<()> {
    let args: Vec<_> = env::args().collect();
    let val = args[1].parse()?;
    let input = io::read_to_string(io::stdin())?;
    let reports = parse_input(&input)?;
    let num_covered = solve_part1(&reports, val);
    println!("[Part 1]: Number of points covered: {num_covered}");

    let frequency = solve_part2(&reports, 0..=2 * val, 0..=2 * val).unwrap();
    println!("[Part 2]: The tuning frequency is {frequency}");

    Ok(())
}
