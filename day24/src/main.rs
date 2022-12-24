//! Advent of Code 2022 Day 24

use std::io;

use day24::{parse_input, solve_part1, solve_part2, Result};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let mut grid = parse_input(&input)?;
    let num_minutes = solve_part1(&mut grid);
    println!("[Part 1] The fewest number of minutes required to reach goal is {num_minutes}");

    let mut grid = parse_input(&input)?;
    let num_minutes = solve_part2(&mut grid);
    println!("[Part 2] The fewest number of minutes required for start -> goal -> start -> goal is {num_minutes}");

    Ok(())
}
