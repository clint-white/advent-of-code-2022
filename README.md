Advent of Code 2022
===================

These are my solutions to [Advent of Code 2022](https://adventofcode.com/2022).
All solutions are written in Rust.  The git tag `v1.0.0` marks the state of the
code when I completed all of the puzzles.  Subsequent commits are continuing
work to improve the style and performance of the solutions and to fix any bugs
I discover.

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

Solves all 25 problems sequentially in an average cumulative time of less than
0.32 seconds on my AMD Ryzen 7 3700 (8C/16T):

```
% hyperfine --warmup 3 'for day in day*; do target/release/$day < $day/data/input > /dev/null; done'
Benchmark 1: for day in day*; do target/release/$day < $day/data/input > /dev/null; done
  Time (mean ± σ):     313.5 ms ±   4.1 ms    [User: 1223.1 ms, System: 26.6 ms]
  Range (min … max):   307.4 ms … 321.3 ms    10 runs
```

Every day's solution runs in under 100ms.  Here are the average times of the
five slowest:

| Day | Time (ms)   | # Threads |
| --- | ----------: | --------: |
| 23  | 98.0 |  1 |
| 15  | 61.2 | 16 |
| 20  | 51.2 |  1 |
| 24  | 29.1 |  1 |
| 16  | 20.8 |  1 |
