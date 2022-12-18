//! Advent of Code 2022 Day 18

use std::io;

use day18::{parse_input, solve_part1, solve_part2, Cube, Result};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let cubes: Vec<Cube<u8>> = parse_input(&input)?;
    let surface_area = solve_part1(cubes.clone());
    println!("[Part 1] Number of faces that are not connected to another cube: {surface_area}");

    let surface_area = solve_part2(cubes);
    println!("[Part 2] Exterior surface area: {surface_area}");

    Ok(())
}
