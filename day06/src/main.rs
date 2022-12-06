//! Advent of Code 2022 Day 6

use std::io::{self, Read};

use day06::{solve_part1, solve_part2};

fn main() -> io::Result<()> {
    let mut buf = Vec::new();
    let _ = io::stdin().read_to_end(&mut buf)?;
    let pos = solve_part1(&buf).unwrap();
    println!("Number of characters processed before first start-of-packet marker: {pos}");

    let pos = solve_part2(&buf).unwrap();
    println!("Number of characters processed before first start-of-message marker: {pos}");

    Ok(())
}
