//! Advent of Code 2022 Day 20

use std::io;

use day20::*;

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let nums = parse_input(&input)?;
    println!("{:?}", &nums);
    println!("{}", nums.len());
    Ok(())
}
