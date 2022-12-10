//! Advent of Code 2022 Day 10

use std::io;

use day10::{parse_input, solve_part1, solve_part2, Result};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let instructions = parse_input(&input)?;

    let ans = solve_part1(&instructions);
    println!("[Part 1] Sum of signal strengths at given cycles: {ans}");

    let crt_display = solve_part2(&instructions);
    println!("[Part 2]");
    println!("{crt_display}");

    Ok(())
}
