//! Advent of Code 2022 Day 5

use std::io;

use day05::{parse_input, solve_part1, solve_part2, Result};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let (mut stacks, instructions) = parse_input(&input)?;

    let mut stacks_part1 = stacks.clone();
    let top_of_stacks = solve_part1(&mut stacks_part1, &instructions)?;
    println!("[Part 1] top of stacks after rearranging: {top_of_stacks}");

    let top_of_stacks = solve_part2(&mut stacks, &instructions)?;
    println!("[Part 2] top of stacks after rearranging: {top_of_stacks}");

    Ok(())
}
