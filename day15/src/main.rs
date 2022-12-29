//! Advent of Code 2022 Day 15

#![allow(clippy::similar_names)]

use std::io;

use day15::{parse_input, solve_part1, solve_part2, Result, SensorReport};

fn main() -> Result<()> {
    let input = io::read_to_string(io::stdin())?;
    let reports = parse_input(&input)?;
    // The example and the actual puzzle input use different additional parameters.  Look at the
    // max radius of the reports to try to determine whether the program input was the example or
    // the real puzzle input, and set the additional parameters accordingly.
    let max_radius = reports.iter().map(SensorReport::radius).max().unwrap_or(0);

    let (y, (xrange, yrange)) = if max_radius == 10 {
        // This looks like the example.
        println!("Using parameters for the example puzzle.");
        (10, (0..=20, 0..=20))
    } else {
        // Othewriwse assume this is the problem input.
        println!("Using parameters for the real puzzle.");
        (2_000_000, (0..=4_000_000, 0..=4_000_000))
    };

    let num_covered = solve_part1(&reports, y);
    println!(
        "[Part 1]: Number of points on row y={y} where a beacon cannot be present: {num_covered}"
    );

    print!(
        "[Part 2]: Tuning frequency for unique beacon in [{}, {}] x [{}, {}]: ",
        xrange.start(),
        xrange.end(),
        yrange.start(),
        yrange.end()
    );
    let frequency = solve_part2(&reports, xrange, yrange)?;
    println!("{frequency}");

    Ok(())
}
