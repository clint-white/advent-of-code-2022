//! Advent of Code 2022 Day 21

use std::io;

use day21::*;

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let exprs = parse_input(&input)?;
    let val = solve_part1(&exprs);
    println!("[Part 1] The value of the root expression is {val}");

    Ok(())
}
