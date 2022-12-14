//! Advent of Code 2022 Day 13

use std::io;

use day13::{parse_input, solve_part1, solve_part2, Result};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let pairs = parse_input(&input)?;
    let index_sum = solve_part1(&pairs);
    println!("[Part 1] Some of indices of in-order pairs: {index_sum}");

    let decoder_key = solve_part2(pairs);
    println!("[Part 2] Decoder key: {decoder_key}");

    Ok(())
}
