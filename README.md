Advent of Code 2022
===================

[![Continuous Integration](https://github.com/clint-white/advent-of-code-2022/actions/workflows/ci.yml/badge.svg)](https://github.com/clint-white/advent-of-code-2022/actions/workflows/ci.yml)

These are my solutions to [Advent of Code 2022](https://adventofcode.com/2022),
written in Rust.  The tag
[v1.0.0](https://github.com/clint-white/advent-of-code-2022/tree/v1.0.0)
marks the state of the code when I completed all of the puzzles.  Subsequent
commits are continuing work to improve the code's style and
[performance](#benchmarks) and to fix bugs.

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

Run the program to solve both parts for a particular day:

```
$ cargo run --release -p day01 < day01/data/input
```

## Benchmarks

Initially I just tried to solve the problems without worrying about how fast
they ran.  But after completing all 25 problems, I worked on optimizing the
performance of some of my slowest solutions and was able to make significant
improvements.

The programs were benchmarked by compiling with `-C target-cpu=native` and run
on an AMD Ryzen 7 3700X.  Runtimes were measured using
[hyperfine](https://github.com/sharkdp/hyperfine).

On my system, the code now solves all 25 problems sequentially in a cumulative
time of less than **0.3 seconds**:

```
% hyperfine --warmup 3 'for day in day*; do target/release/$day < $day/data/input; done'
Benchmark 1: for day in day*; do target/release/$day < $day/data/input; done
  Time (mean ± σ):     294.9 ms ±   2.7 ms    [User: 1203.5 ms, System: 24.7 ms]
  Range (min … max):   290.9 ms … 299.0 ms    10 runs
```

No day's solution now takes more than 100 ms.  These are the slowest:

| Day | Mean [ms] | Min [ms] | Max [ms] |
|:---|---:|---:|---:|
| `day23` | 92.5 ± 2.1 | 89.2 | 98.9 |
| `day15` | 60.8 ± 1.0 | 59.7 | 64.4 |
| `day20` | 39.2 ± 1.8 | 37.9 | 46.1 |
| `day24` | 30.4 ± 0.8 | 29.7 | 34.4 |
| `day16` | 20.6 ± 0.6 | 20.1 | 23.4 |

All other days' solutions run in average times of less than 10 ms each.
