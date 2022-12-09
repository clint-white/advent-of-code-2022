//! Advent of Code 2022 Day 8

use std::io;

use day08::{parse_input, solve_part1, solve_part2, Result};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let array = parse_input(&input)?;

    let num_visible = solve_part1(array.view());
    println!("Number of trees visible from the exterior: {num_visible}");

    let scenic_score = solve_part2(array.view());
    println!("Greatest scenic score: {scenic_score}");

    Ok(())
}
