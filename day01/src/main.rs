//! Advent of Code 2022 Day 1

use std::io;

use day01::{max_sum, read_input, sum_topk_sums, Result};

fn main() -> Result<()> {
    let mut stdin = io::stdin().lock();
    let values = read_input(&mut stdin)?;

    let best = max_sum(&values).unwrap();
    println!("greatest sum: {best}");

    let best3 = sum_topk_sums(&values, 3);
    println!("sum of top 3 sums: {best3}");
    Ok(())
}
