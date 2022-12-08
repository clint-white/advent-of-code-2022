//! Advent of Code 2022 Day 7

use std::io;

use day07::{build_fs_tree, parse_input, solve_part1, solve_part2, Result};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let commands = parse_input(&input)?;
    let root = build_fs_tree(&commands);
    let size = solve_part1(&root);
    println!("[Part 1] Some of sizes of directories of total size at most 100000: {size}");

    if let Some(size) = solve_part2(&root) {
        println!("[Part 2] Total size of smallest directory that could be deleted: {size}");
    } else {
        println!("[Part 2] No directory large enough to free sufficient space");
    }
    Ok(())
}
