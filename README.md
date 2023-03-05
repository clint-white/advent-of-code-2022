Advent of Code 2022
===================

[![Continuous Integration](https://github.com/clint-white/advent-of-code-2022/actions/workflows/ci.yml/badge.svg)](https://github.com/clint-white/advent-of-code-2022/actions/workflows/ci.yml)

These are my solutions to [Advent of Code 2022](https://adventofcode.com/2022),
written in Rust.  The tag
[`v1.0.0`](https://github.com/clint-white/advent-of-code-2022/tree/v1.0.0)
marks the state of the code when I completed all of the puzzles.  Subsequent
commits are continuing work to improve the code's style and
[performance](#benchmarks) and to fix bugs.

Each day's puzzle is implemented as a package with a binary and a library
crate.  All examples provided as part of the puzzle descriptions are used as
unit tests, as are the actual puzzle inputs and answers.

Run the tests for a particular day:

```console
$ cargo test -p day01
```

Run the tests for all the days:

```console
$ cargo test
```

The example and actual puzzle inputs are in files in the `data` subdirectory of
each day's package.  The main programs take no arguments and read their input
from stdin.

Run the program to solve both parts for a particular day:

```console
$ cargo run --release -p day01 < day01/data/input
```

## Benchmarks

Initially I just tried to solve the problems without worrying about how fast
they ran.  But after completing all 25 problems, I worked on optimizing the
performance of my slowest solutions.  Here are some current benchmarks.

On an AMD Ryzen 7 3700X, the solutions to all 25 problems run sequentially in a
cumulative time of **0.21 seconds**:

```console
% hyperfine --warmup 10 'for day in day*; do target/release/$day < $day/data/input; done'
Benchmark 1: for day in day*; do target/release/$day < $day/data/input; done
  Time (mean ± σ):     209.6 ms ±   6.3 ms    [User: 220.0 ms, System: 25.8 ms]
  Range (min … max):   200.1 ms … 221.0 ms    14 runs
```

Every solution completes in less than 100 ms, and all but the following complete
in under 10 ms:

| Day | Mean [ms] | Min [ms] | Max [ms] |
|:---|---:|---:|---:|
| `day23` | 92.5 ± 2.1 | 89.2 | 98.9 |
| `day24` | 30.4 ± 0.8 | 29.7 | 34.4 |
| `day16` | 20.6 ± 0.6 | 20.1 | 23.4 |
| `day20` | 12.1 ± 0.4 | 11.6 | 13.9 |

On a Raspberry Pi 4 Model B `aarch64`, the solutions to all 25 problems run
consecutively in under 1 second:

```console
% hyperfine --warmup 10 'for day in day*; do target/release/$day < $day/data/input; done'
Benchmark 1: for day in day*; do target/release/$day < $day/data/input; done
  Time (mean ± σ):     943.2 ms ±   4.6 ms    [User: 883.3 ms, System: 124.1 ms]
  Range (min … max):   938.7 ms … 951.3 ms    10 runs
```

These benchmarks were performed using
[hyperfine](https://github.com/sharkdp/hyperfine).  The code was compiled with
`-C target-cpu=native`.
