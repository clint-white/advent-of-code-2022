//! Advent of Code 2022 Day 12

use std::io;

use day12::{parse_input, solve_part1, solve_part2, Result};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let height_map = parse_input(&input)?;
    let shortest_path = solve_part1(&height_map);
    if let Some(n) = shortest_path {
        println!("[Part 1] Shortest path from source to sink has length {n}");
    } else {
        println!("[Part 1] Source and sink are not in the same component");
    }
    let shortest_path = solve_part2(&height_map);
    if let Some(n) = shortest_path {
        println!("[Part 2] Shortest path from sink to some point of 0 elevation: {n}");
    } else {
        println!("[Part 2] Sink is not in the same component as any point of zero elevation");
    }

    Ok(())
}
