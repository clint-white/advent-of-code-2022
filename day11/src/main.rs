//! Advent of Code 2022 Day 11

use std::io;

use day11::{parse_input, solve_part1, solve_part2, Result};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let mut monkeys = parse_input(&input)?;
    let monkey_business = solve_part1(&mut monkeys);
    println!("[Part 1] Level of monkey business after 20 rounds: {monkey_business}");

    let mut monkeys = parse_input(&input)?;
    let monkey_business = solve_part2(&mut monkeys);
    println!("[Part 2] Level of monkey business after 10000 rounds: {monkey_business}");

    Ok(())
}
