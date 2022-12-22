//! Advent of Code 2022 Day 21

use std::io;

use day21::{parse_input, solve_part1, solve_part2, Result};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let exprs = parse_input(&input)?;
    let val = solve_part1(&exprs);
    println!("[Part 1] The value of the root expression is {val}");

    if let Some(ans) = solve_part2(&exprs) {
        println!("[Part 2] x = {ans}");
    } else {
        println!("[Part 2] Unable to fully solve equation");
    }

    Ok(())
}
