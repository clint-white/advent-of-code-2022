Advent of Code 2022
===================

These are my solutions to [Advent of Code 2022](https://adventofcode.com/2022).
All solutions are written in Rust.  The git tag "v1.0.0" marks the state of the
code when I completed all of the puzzles.  Subsequent commits are continuing
work to improve the style and performance of the solutions and to fix any bugs
I discover.

Each day's puzzle is implemented as a separate package with a binary and a
library crate.  All examples provided as part of the puzzle descriptions are
used as unit tests, as are the actual puzzle inputs and answers.

To run the tests for a particular day, run the following from this repository's
root directory:

```
$ cargo test -p day01
```

Some of the tests are slow as the code is compiled in debug mode for the tests.

The example and actual puzzle inputs appear as files in the `data` subdirectory
of each day's package.  The main programs take no arguments and read their
input from stdin.  To run the solutions for both parts of a puzzle for a
particular day, run the following, again from the root directory of the
repository:

```
$ cargo run --release -p day01 < day01/data/input
```

Similarly, to run the solution on the example puzzle:

```
$ cargo run --release -p day01 < day01/data/example
```
