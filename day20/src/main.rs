//! Advent of Code 2022 Day 20

use std::io;

use day20::{parse_input, solve_part1, solve_part2, Result};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let mut nums = parse_input(&input)?;
    let mut nums1 = nums.clone();
    let s = solve_part1(&mut nums1).expect("the list of numbers contains 0");
    println!("[Part 1] Sum of coordinates: {s}");

    let s = solve_part2(&mut nums).expect("the list of numbers contains 0");
    println!("[Part 2] Sum of coordinates: {s}");

    Ok(())
}
