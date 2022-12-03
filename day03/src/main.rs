//! Advent of Code 2022 Day 3

use std::io;

use day03::{read_input, solve_part1, solve_part2, Result};

fn main() -> Result<()> {
    let s = io::read_to_string(io::stdin())?;
    let rucksacks = read_input(&s)?;

    let priority = solve_part1(&rucksacks)?;
    println!("Total priority of mispacked items: {priority}");

    let priority = solve_part2(&rucksacks)?;
    println!("Total priority of group badges: {priority}");

    Ok(())
}
