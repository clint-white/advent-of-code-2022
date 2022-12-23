//! Advent of Code 2022 Day 23

use std::io;

use day23::*;

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let mut elves = parse_input(&input)?;
    let empty_tiles = solve_part1(&mut elves);
    println!("[Part 1] The number of empty tiles after 10 rounds is {empty_tiles}");

    let mut elves = parse_input(&input)?;
    let round = solve_part2(&mut elves);
    println!("[Part 2] The first round where no elves move is {round}");

    Ok(())
}
