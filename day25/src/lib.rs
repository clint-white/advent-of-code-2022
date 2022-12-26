//! Solutions to [Advent of Code 2022 Day 25](https://adventofcode.com/2022/day/25).

use std::io;
use std::ops::Neg;

use thiserror::Error;

/// The error type for operations in this crate.
///
/// This type is modeled after [`IntErrorKind`].
///
/// [`IntErrorKind`]: std::num::IntErrorKind
#[derive(Debug, Error)]
pub enum Error {
    /// An underlying [`io::Error`].
    #[error("I/O error")]
    Io(#[from] io::Error),

    /// The string being parsed is empty.
    #[error("The string being parsed is empty")]
    Empty,

    /// Contains an invalid digit.
    #[error("Invalid digit: '{0}'")]
    InvalidDigit(char),

    /// The integer is too large for the width of the type.
    #[error("Positive overflow")]
    PosOverflow,

    /// The integer is too small for the width of the type.
    #[error("Negative overflow")]
    NegOverflow,
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

macro_rules! from_str_snafu {
    ($($t:ty)*) => ($(
            fn from_str_snafu(s: &str) -> Result<Self> {
                let mut ans = 0 as $t;
                if s.is_empty() {
                    return Err(Error::Empty);
                }
                for c in s.chars() {
                    let digit = parse_snafu_digit(c)?;
                    ans = ans.checked_mul(5 as $t).ok_or(Error::PosOverflow)?;
                    if digit > 0 {
                        ans = ans.checked_add(digit as $t).ok_or(Error::PosOverflow)?;
                    } else if digit < 0 {
                        ans = ans.checked_sub(digit.abs() as $t).ok_or(Error::NegOverflow)?;
                    }
                }
                Ok(ans)
            }
    )*)
}

macro_rules! snafu_digits_le {
    ($($t:ty)*) => ($(
            /// Returns a vector of "SNAFU" digits for `n >= 0`.
            fn snafu_digits_le(mut n: $t) -> Vec<i8> {
                let mut digits_le = vec![];
                if n == 0 {
                    digits_le.push(0);
                } else {
                    while n > 0 {
                        let mut rem = (n % 5) as i8;
                        if rem > 2 {
                            rem -= 5;
                            n += 5;
                        }
                        digits_le.push(rem);
                        n /= 5;
                    }
                };
                digits_le
            }
    )*)
}

// impl Snafu for signed integer types.
macro_rules! snafu_impl_signed {
    ($($t:ty)*) => ($(
            impl Snafu for $t {
                from_str_snafu! { $t }

                fn to_string_snafu(&self) -> String {
                    snafu_digits_le! { $t }

                    let is_negative = self.is_negative();
                    let n = self.abs();
                    let mut digits_le = snafu_digits_le(n);
                    if is_negative {
                        digits_le.iter_mut().for_each(|digit| *digit = digit.neg());
                    }
                    digits_le.into_iter().rev().map(snafu_digit_to_char).collect()
                }
            }
    )*)
}

// impl Snafu for unsigned integer types.
macro_rules! snafu_impl_unsigned {
    ($($t:ty)*) => ($(
            impl Snafu for $t {
                from_str_snafu! { $t }

                fn to_string_snafu(&self) -> String {
                    snafu_digits_le! { $t }

                    let digits_le = snafu_digits_le(*self);
                    digits_le.into_iter().rev().map(snafu_digit_to_char).collect()
                }
            }
    )*)
}

snafu_impl_signed! { isize i8 i16 i32 i64 i128 }
snafu_impl_unsigned! { usize u8 u16 u32 u64 u128 }

fn parse_snafu_digit(digit: char) -> Result<i8> {
    match digit {
        '2' => Ok(2),
        '1' => Ok(1),
        '0' => Ok(0),
        '-' => Ok(-1),
        '=' => Ok(-2),
        _ => Err(Error::InvalidDigit(digit)),
    }
}

// `digit` must be known to be in the range -2..=2.
fn snafu_digit_to_char(digit: i8) -> char {
    match digit {
        2 => '2',
        1 => '1',
        0 => '0',
        -1 => '-',
        -2 => '=',
        _ => unreachable!(),
    }
}

/// Parses an integer in "SNAFU" format.
///
/// # Errors
///
/// Returns an error if any of the digits are invalid or if the integers overflow or underflow the
/// width of the type.
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
            ("-", -1),
            ("=", -2),
            ("-2", -3),
            ("-1", -4),
            ("-0", -5),
            ("--", -6),
        ];
        for (s, n) in cases {
            let parsed = i32::from_str_snafu(s)?;
            assert_eq!(parsed, n);
        }
        Ok(())
    }

    #[test]
    fn test_parsing_unsigned() -> Result<()> {
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
            let parsed = u32::from_str_snafu(s)?;
            assert_eq!(parsed, n);
        }
        Ok(())
    }

    #[test]
    fn test_parsing_unsigned_errors() {
        // Errors parsing negative integers as an unsigned type.
        let result = u32::from_str_snafu("--");
        assert!(matches!(result, Err(Error::NegOverflow)));

        // Overflow the width of the type.
        let result = u8::from_str_snafu("1=11-2");
        assert!(matches!(result, Err(Error::PosOverflow)));

        // Empty string.
        let result = u8::from_str_snafu("");
        assert!(matches!(result, Err(Error::Empty)));
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
            ("-", -1),
            ("=", -2),
            ("-2", -3),
            ("-1", -4),
            ("-0", -5),
            ("--", -6),
        ];
        for (s, n) in cases {
            let formatted = n.to_string_snafu();
            assert_eq!(formatted, s);
        }
        Ok(())
    }

    #[test]
    fn test_formatting_unsigned() -> Result<()> {
        let cases = [
            ("1=-0-2", 1747_u32),
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
