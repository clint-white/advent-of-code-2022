//! Advent of Code 2022 Day 14

use std::io;

use day14::*;

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let paths = parse_input(&input)?;
    let count = solve_part1(&paths)?;
    println!("[Part 1] Number of grands of sand that come to rest: {count}");

    let count = solve_part2(&paths)?;
    println!("[Part 2] Number of grands of sand that come to rest: {count}");

    Ok(())
}
