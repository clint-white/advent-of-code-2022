//! Advent of Code 2022 Day 17

use std::io;

use day17::{parse_input, solve_part1, solve_part2, Result};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let shifts = parse_input(&input)?;
    let height = solve_part1(shifts);
    println!("[Part 1] Height of rock tower after 2022 rocks: {height}");

    let shifts = parse_input(&input)?;
    if let Some(height) = solve_part2(shifts, 1_000_000_000_000) {
        println!("[Part 1] Height of rock tower after  1_000_000_000_000 rocks: {height}");
    } else {
        println!("[Part 2] Unable to find the height of the tower");
    }

    Ok(())
}
