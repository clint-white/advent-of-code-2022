//! Solutions to [Advent of Code 2022 Day 25](https://adventofcode.com/2022/day/25).

use std::io;
use std::ops::Neg;

use thiserror::Error;

/// The error type for operations in this crate.
#[derive(Debug, Error)]
pub enum Error {
    /// An underlying [`io::Error`].
    #[error("I/O error")]
    Io(#[from] io::Error),

    /// Contains an invalid digit.
    #[error("Invalid digit: '{0}'")]
    InvalidDigit(char),
    // XXX Add error cases for overflow, as in `std::num::ParseIntError`.
}

/// A specialized [`Result`] type for operations in this crate.
///
/// [`Result`]: std::result::Result
pub type Result<T> = std::result::Result<T, Error>;

/// A trait for types that can be represented by "SNAFU" formatted strings.
pub trait Snafu: Sized {
    /// Parses a "SNAFU" formatted string.
    ///
    /// # Errors
    ///
    /// Returns an error if `s` contains an invalid "SNAFU" digit.
    fn from_str_snafu(s: &str) -> Result<Self>;

    /// Writes an integer as a string in "SNAFU" format.
    fn to_string_snafu(&self) -> String;
}

macro_rules! snafu_impl {
    ($($t:ty)*) => ($(
            impl Snafu for $t {
                fn from_str_snafu(s: &str) -> Result<Self> {
                    let digits = parse_snafu_digits(s)?;
                    // XXX This works only for signed types.
                    let n = digits
                        .iter()
                        .enumerate()
                        .map(|(power, &digit)| digit as $t * (5 as $t).pow(power as u32))
                        .sum();
                    Ok(n)
                }

                fn to_string_snafu(&self) -> String {
                    let is_negative = self.is_negative();
                    let mut n = self.abs();
                    let mut digits = if n == 0 {
                        vec![0]
                    } else {
                        let mut digits = Vec::new();
                        while n > 0 {
                            let mut rem = (n % 5) as i8;
                            if rem > 2 {
                                rem -= 5;
                                n += 5;
                            }
                            digits.push(rem);
                            n /= 5;
                        }
                        digits
                    };
                    if is_negative {
                        digits.iter_mut().for_each(|digit| *digit = digit.neg());
                    }
                    fmt_snafu_digits(&digits)
                }
            }
    )*)
}

// XXX Fix `from_str_snafu()` so that it works for unsigned types as well.
snafu_impl! { isize i8 i16 i32 i64 i128 }

fn parse_snafu_digits(s: &str) -> Result<Vec<i8>> {
    s.chars()
        .rev()
        .map(|c| match c {
            '2' => Ok(2),
            '1' => Ok(1),
            '0' => Ok(0),
            '-' => Ok(-1),
            '=' => Ok(-2),
            _ => Err(Error::InvalidDigit(c)),
        })
        .collect()
}

fn fmt_snafu_digits(digits: &[i8]) -> String {
    digits
        .iter()
        .rev()
        .map(|&digit| match digit {
            2 => '2',
            1 => '1',
            0 => '0',
            -1 => '-',
            -2 => '=',
            _ => unreachable!(),
        })
        .collect()
}

/// Parses an integer in "SNAFU" format.
///
/// # Errors
///
/// Returns an error if any of the digits are invalid.
pub fn parse_input<T: Snafu>(s: &str) -> Result<Vec<T>> {
    s.lines().map(Snafu::from_str_snafu).collect()
}

#[must_use]
pub fn solve_part1(xs: &[i64]) -> String {
    let sum: i64 = xs.iter().sum();
    sum.to_string_snafu()
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_parsing_signed() -> Result<()> {
        let cases = [
            ("1=-0-2", 1747),
            ("12111", 906),
            ("2=0=", 198),
            ("21", 11),
            ("2=01", 201),
            ("111", 31),
            ("20012", 1257),
            ("112", 32),
            ("1=-1=", 353),
            ("1-12", 107),
            ("12", 7),
            ("1=", 3),
            ("122", 37),
            ("1=11-2", 2022),
            ("1-0---0", 12345),
            ("1121-1110-1=0", 314159265),
        ];
        for (s, n) in cases {
            let parsed = i32::from_str_snafu(s)?;
            assert_eq!(parsed, n);
        }
        Ok(())
    }

    #[test]
    fn test_formatting_signed() -> Result<()> {
        let cases = [
            ("1=-0-2", 1747_i32),
            ("12111", 906),
            ("2=0=", 198),
            ("21", 11),
            ("2=01", 201),
            ("111", 31),
            ("20012", 1257),
            ("112", 32),
            ("1=-1=", 353),
            ("1-12", 107),
            ("12", 7),
            ("1=", 3),
            ("122", 37),
            ("1=11-2", 2022),
            ("1-0---0", 12345),
            ("1121-1110-1=0", 314159265),
        ];
        for (s, n) in cases {
            let formatted = n.to_string_snafu();
            assert_eq!(formatted, s);
        }
        Ok(())
    }

    #[test]
    fn test_part1_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let xs = parse_input::<i16>(&input)?;
        let sum: i16 = xs.into_iter().sum();
        let s = sum.to_string_snafu();
        assert_eq!(s, "2=-1=0");
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let xs = parse_input::<i64>(&input)?;
        let sum: i64 = xs.into_iter().sum();
        let s = sum.to_string_snafu();
        assert_eq!(s, "2-0-020-1==1021=--01");
        Ok(())
    }
}
