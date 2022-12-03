//! Advent of Code 2022 Day 2

use std::io;

use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error("I/O error")]
    Io(#[from] io::Error),

    #[error("Invalid input")]
    Invalid,
}

pub type Result<T> = std::result::Result<T, Error>;

/// The possible hand shapes in the game of Rock, Paper, Scissors.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Shape {
    Rock = 1,
    Paper = 2,
    Scissors = 3,
}

impl Shape {
    /// Returns the outcome obtained by `self` when played against `other`.
    #[must_use]
    pub const fn outcome(&self, other: &Self) -> Outcome {
        use Shape::{Paper, Rock, Scissors};

        match (self, other) {
            (Rock, Scissors) | (Scissors, Paper) | (Paper, Rock) => Outcome::Win,
            (Scissors, Rock) | (Paper, Scissors) | (Rock, Paper) => Outcome::Loss,
            (Rock, Rock) | (Scissors, Scissors) | (Paper, Paper) => Outcome::Draw,
        }
    }

    #[must_use]
    pub const fn score(&self) -> i32 {
        *self as i32
    }
}

/// The outcomes of a round of Rock, Paper, Scissors.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    Loss = 0,
    Draw = 3,
    Win = 6,
}

impl Outcome {
    #[must_use]
    pub const fn score(&self) -> i32 {
        *self as i32
    }

    /// Returns the shape that will obtain outcome `self` when played against shape `other`.
    #[must_use]
    pub const fn shape(&self, other: &Shape) -> Shape {
        use Outcome::{Draw, Loss, Win};
        use Shape::{Paper, Rock, Scissors};

        match (self, other) {
            (Loss, Paper) | (Draw, Rock) | (Win, Scissors) => Rock,
            (Loss, Rock) | (Draw, Scissors) | (Win, Paper) => Scissors,
            (Loss, Scissors) | (Draw, Paper) | (Win, Rock) => Paper,
        }
    }
}

/// Parses a "strategy guide" into a vector of pairs of `chars`.
///
/// # Examples
///
/// ```
/// # use day02::Error;
/// use day02::parse_input;
///
/// let s = "A Y\nB X\nC Z";
/// let expected = vec![('A', 'Y'), ('B', 'X'), ('C', 'Z')];
/// let parsed = parse_input(&s);
/// assert!(parsed.is_ok());
/// assert_eq!(parsed.unwrap(), expected);
/// # Ok::<(), Error>(())
/// ```
///
/// # Errors
///
/// Returns [`Error::Invalid`] is any line consists of more than three bytes or if the middle byte
/// is not unicode whitespace.
pub fn parse_input(s: &str) -> Result<Vec<(char, char)>> {
    let mut pairs = Vec::new();
    for line in s.lines() {
        let bytes = line.as_bytes();
        if bytes.len() != 3 {
            return Err(Error::Invalid);
        }
        let a = char::from(bytes[0]);
        let b = char::from(bytes[1]);
        let c = char::from(bytes[2]);
        if !b.is_whitespace() {
            return Err(Error::Invalid);
        }
        pairs.push((a, c));
    }
    Ok(pairs)
}

/// Parse a `char` as a [`Shape`].
///
/// # Errors
///
/// Returns [`Error::Invalid`] if the `char` is not one of `'A'`, `'B'`, `'C'`.
pub const fn parse_shape(c: char) -> Result<Shape> {
    match c {
        'A' => Ok(Shape::Rock),
        'B' => Ok(Shape::Paper),
        'C' => Ok(Shape::Scissors),
        _ => Err(Error::Invalid),
    }
}

/// Decodes a `char` as a [`Shape`].
///
/// # Errors
///
/// Returns [`Error::Invalid`] if the `char` is not one of `'X'`, `'Y'`, `'Z'`.
pub const fn decode_as_shape(c: char) -> Result<Shape> {
    match c {
        'X' => Ok(Shape::Rock),
        'Y' => Ok(Shape::Paper),
        'Z' => Ok(Shape::Scissors),
        _ => Err(Error::Invalid),
    }
}

/// Decodes a `char` as a [`Outcome`].
///
/// # Errors
///
/// Returns [`Error::Invalid`] if the `char` is not one of `'X'`, `'Y'`, `'Z'`.
pub const fn decode_as_outcome(c: char) -> Result<Outcome> {
    match c {
        'X' => Ok(Outcome::Loss),
        'Y' => Ok(Outcome::Draw),
        'Z' => Ok(Outcome::Win),
        _ => Err(Error::Invalid),
    }
}

/// Interprets a list of pairs of characters as a strategy guide.
///
/// The two closures are used for decoding the two columns of each line of the guide.
///
/// # Errors
///
/// Returns [`Error::Invalid`] if any of the first characters is not one of `'A'`, `'B'`, `'C'` or
/// any of the second characters is not one of `'X'`, `'Y'`, `'Z'`.
pub fn interpret_log<F, G, T, U>(log: &[(char, char)], mut f: F, mut g: G) -> Result<Vec<(T, U)>>
where
    F: FnMut(char) -> Result<T>,
    G: FnMut(char) -> Result<U>,
{
    log.iter()
        .map(|&(a, b)| match (f(a), g(b)) {
            (Ok(t), Ok(u)) => Ok((t, u)),
            (Err(e), _) | (_, Err(e)) => Err(e),
        })
        .collect()
}

#[must_use]
pub fn total_score1(strategy: &[(Shape, Shape)]) -> i32 {
    strategy
        .iter()
        .map(|(opponent, us)| us.outcome(opponent).score() + us.score())
        .sum()
}

#[must_use]
pub fn total_score2(strategy: &[(Shape, Outcome)]) -> i32 {
    strategy
        .iter()
        .map(|(opponent, outcome)| outcome.shape(opponent).score() + outcome.score())
        .sum()
}

/// Solves part 1.
pub fn solve_p1(input: &str) -> Result<i32> {
    let log = parse_input(input)?;
    let strategy = interpret_log(&log, parse_shape, decode_as_shape)?;
    let score = total_score1(&strategy);
    Ok(score)
}

/// Solves part 2.
pub fn solve_p2(input: &str) -> Result<i32> {
    let log = parse_input(input)?;
    let strategy = interpret_log(&log, parse_shape, decode_as_outcome)?;
    let score = total_score2(&strategy);
    Ok(score)
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_part1_example() -> Result<()> {
        let s = "A Y\nB X\nC Z";
        let log = parse_input(s)?;
        let strategy = interpret_log(&log, parse_shape, decode_as_shape)?;
        let score = total_score1(&strategy);
        assert_eq!(score, 15);
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let s = fs::read_to_string("data/input")?;
        let log = parse_input(&s)?;
        let strategy = interpret_log(&log, parse_shape, decode_as_shape)?;
        let score = total_score1(&strategy);
        assert_eq!(score, 11873);
        Ok(())
    }

    #[test]
    fn test_part2_example() -> Result<()> {
        let s = "A Y\nB X\nC Z";
        let log = parse_input(s)?;
        let strategy = interpret_log(&log, parse_shape, decode_as_outcome)?;
        let score = total_score2(&strategy);
        assert_eq!(score, 12);
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let s = fs::read_to_string("data/input")?;
        let log = parse_input(&s)?;
        let strategy = interpret_log(&log, parse_shape, decode_as_outcome)?;
        let score = total_score2(&strategy);
        assert_eq!(score, 12014);
        Ok(())
    }
}
