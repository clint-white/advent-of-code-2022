Advent of Code 2022
===================

These are my solutions to [Advent of Code 2022](https://adventofcode.com/2022).
All solutions are written in Rust.  The git tag `v1.0.0` marks the state of the
code when I completed all of the puzzles.  Subsequent commits are continuing
work to improve the style and performance of the solutions and to fix any bugs
I discover.

## Run the code

Each day's puzzle is implemented as a package with a binary and a library
crate.  All examples provided as part of the puzzle descriptions are used as
unit tests, as are the actual puzzle inputs and answers.

Run the tests for a particular day:

```
$ cargo test -p day01
```

Run the tests for all the days:

```
$ cargo test
```

The example and actual puzzle inputs are in files in the `data` subdirectory of
each day's package.  The main programs take no arguments and read their input
from stdin.

Run the solution for a particular day on my input file:

```
$ cargo run --release -p day01 < day01/data/input
```

## Benchmarks

Solves all 25 problems in a cumulative time of under 0.6s:

```
% hyperfine --warmup 3 'for day in day*; do target/release/$day < $day/data/input > /dev/null; done'
Benchmark 1: for day in day*; do target/release/$day < $day/data/input > /dev/null; done
  Time (mean ± σ):     512.3 ms ±  46.5 ms    [User: 1436.2 ms, System: 21.5 ms]
  Range (min … max):   459.5 ms … 586.7 ms    10 runs
```
