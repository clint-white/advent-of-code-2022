//! Advent of Code 2022 Day 17

use std::io;

use day17::*;

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let shifts = parse_input(&input)?;
    let height = solve_part1(&shifts);
    println!("[Part 1] Height of rock tower after 2022 rocks: {height}");

    Ok(())
}
