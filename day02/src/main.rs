//! Advent of Code 2022 Day 2

use std::io;

use day02::{solve_p1, solve_p2, Result};

fn main() -> Result<()> {
    let s = io::read_to_string(io::stdin())?;
    let score = solve_p1(&s)?;
    println!("answer for part 1: {score}");

    let score = solve_p2(&s)?;
    println!("answer for part 2: {score}");
    Ok(())
}
