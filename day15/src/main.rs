//! Advent of Code 2022 Day 15

use std::io;

use day15::*;

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let reports = parse_input(&input)?;
    // XXX Read the y-coordinate as a program argument.
    let num_covered = solve_part1(&reports, 2_000_000);
    println!("[Part 1]: Number of points covered: {num_covered}");

    Ok(())
}
