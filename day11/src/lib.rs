//! Solutions to [Advent of Code 2022 Day 11](https://adventofcode.com/2022/day/11).

use std::collections::VecDeque;
use std::io;
use std::num::ParseIntError;

use once_cell::sync::OnceCell;
use regex::Regex;
use thiserror::Error;

macro_rules! regex {
    ($re:literal $(,)?) => {{
        static RE: OnceCell<Regex> = OnceCell::new();
        RE.get_or_init(|| Regex::new($re).unwrap())
    }};
}

/// The error type for operations in this crate.
#[derive(Debug, Error)]
pub enum Error {
    /// An underlying [`io::Error`].
    #[error("I/O error")]
    Io(#[from] io::Error),

    /// The input ended unexpectedly
    #[error("Unexpected end of input")]
    UnexpectedEndOfInput,

    /// An error parsing an integer
    #[error("Error parsing integer")]
    ParseInt(#[from] ParseIntError),

    /// An general parse error
    #[error("Parse error on line: '{0}'")]
    Parse(String),
}

/// A specialized [`Result`] type for operations in this crate.
///
/// [`Result`]: std::result::Result
pub type Result<T> = std::result::Result<T, Error>;

pub type Worry = u64;

pub type Predicate = Box<dyn Fn(Worry) -> bool>;
pub type Operation = Box<dyn Fn(Worry) -> Worry>;

pub struct Monkey {
    items: VecDeque<Worry>,
    op: Operation,
    predicate: Predicate,
    modulus: Worry,
    send_to: [usize; 2],
    inspection_count: usize,
}

impl Monkey {
    /// Returns the number of items the monkey has inspected.
    #[must_use]
    #[inline]
    pub fn inspection_count(&self) -> usize {
        self.inspection_count
    }

    /// Iterates over the monkey's items.
    pub fn items(&self) -> impl Iterator<Item = Worry> + '_ {
        self.items.iter().copied()
    }

    /// Inspects the next item
    ///
    /// Returns the worry level of the item and the index of the monkey to which it is thrown, or
    /// `None` if there are no remaining items.
    pub fn inspect_next_item<R>(&mut self, relax: R) -> Option<(Worry, usize)>
    where
        R: Fn(Worry) -> Worry,
    {
        let item = self.items.pop_front()?;
        let worry = relax((self.op)(item));
        let next = self.send_to[usize::from((self.predicate)(worry))];
        self.inspection_count += 1;
        Some((worry, next))
    }

    pub fn push(&mut self, item: Worry) {
        self.items.push_back(item);
    }

    #[must_use]
    pub fn modulus(&self) -> Worry {
        self.modulus
    }
}

/// Runs the `i`th monkey's turn and returns the number of items inspected.
///
/// # Panics
///
/// Panics if `i` is greater than or equal to the number of monkeys.
pub fn take_turn<R>(monkeys: &mut [Monkey], relax: R, i: usize) -> usize
where
    R: Fn(Worry) -> Worry,
{
    let mut n = 0;
    while let Some((item, destination)) = monkeys[i].inspect_next_item(&relax) {
        monkeys[destination].push(item);
        n += 1;
    }
    n
}

pub fn do_round<R>(monkeys: &mut [Monkey], relax: R)
where
    R: Fn(Worry) -> Worry,
{
    for i in 0..monkeys.len() {
        take_turn(monkeys, &relax, i);
    }
}

pub fn solve_part1(monkeys: &mut [Monkey]) -> usize {
    for _ in 0..20 {
        do_round(monkeys, |x| x / 3);
    }
    let mut num_inspected: Vec<_> = monkeys.iter().map(Monkey::inspection_count).collect();
    num_inspected.sort_unstable_by(|a, b| a.cmp(b).reverse());
    num_inspected[0] * num_inspected[1]
}

pub fn solve_part2(monkeys: &mut [Monkey]) -> usize {
    let m: Worry = monkeys.iter().map(Monkey::modulus).product();
    for _ in 0..10_000 {
        do_round(monkeys, |x| x % m);
    }
    let mut num_inspected: Vec<_> = monkeys.iter().map(Monkey::inspection_count).collect();
    num_inspected.sort_unstable_by(|a, b| a.cmp(b).reverse());
    num_inspected[0] * num_inspected[1]
}

/// Parses puzzle into into a vector of [`Monkey`]s.
///
/// # Errors
///
/// This function returns an error if it could not parse the input as blank-line separated
/// [`Monkey`]s.
pub fn parse_input(s: &str) -> Result<Vec<Monkey>> {
    let blank_lines = regex!(r"\n{2,}");
    blank_lines.split(s).map(parse_monkey).collect()
}

/// Parses a single [`Monkey`] description.
///
/// # Errors
///
/// This function returns an error if `s` is not formatted properly.
pub fn parse_monkey(s: &str) -> Result<Monkey> {
    let mut lines = s.lines();
    parse_monkey_start(next_line(&mut lines)?)?;
    let items = parse_starting_items(next_line(&mut lines)?)?;
    let op = parse_op(next_line(&mut lines)?)?;
    let (modulus, predicate) = parse_predicate(next_line(&mut lines)?)?;
    let send_to = parse_send_to(next_line(&mut lines)?, next_line(&mut lines)?)?;
    let monkey = Monkey {
        items,
        op,
        predicate,
        modulus,
        send_to,
        inspection_count: 0,
    };
    Ok(monkey)
}

/// Expects to find the start-of-monkey line
///
/// ```text
/// Monkey 0:
/// ```
fn parse_monkey_start(s: &str) -> Result<()> {
    let re = regex!(r"^Monkey \d+:$");
    if re.is_match(s) {
        Ok(())
    } else {
        Err(Error::Parse(s.into()))
    }
}

/// Expects to find a line listing the starting items.
///
/// The line should like like the following:
///
/// ```text
///   Starting items: 1, 2, 3
/// ```
fn parse_starting_items(s: &str) -> Result<VecDeque<Worry>> {
    let starting_items = regex!(r"\s*Starting items:\s*(?P<list>\d+(,\s*\d+)*)");
    let caps = starting_items
        .captures(s)
        .ok_or_else(|| Error::Parse(s.into()))?;
    let list = &caps["list"];
    let comma = regex!(r",\s*");
    comma
        .split(list)
        .map(|digits| digits.parse::<Worry>().map_err(Into::into))
        .collect()
}

fn parse_op(s: &str) -> Result<Operation> {
    let re = regex!(
        r"\s*Operation:\s*new\s*=\s*(?P<left>old|\d+)\s*(?P<operator>\+|\*)\s*(?P<right>old|\d+)"
    );
    let caps = re.captures(s).ok_or_else(|| Error::Parse(s.into()))?;
    let left = &caps["left"];
    let operator = &caps["operator"];
    let right = &caps["right"];
    let closure: Box<dyn Fn(Worry) -> Worry> = match (left, operator, right) {
        ("old", "+", "old") => Box::new(|x| x + x),
        ("old", "+", literal) => {
            let arg = literal.parse::<Worry>()?;
            Box::new(move |x| x + arg)
        }
        ("old", "*", "old") => Box::new(|x| x * x),
        ("old", "*", literal) => {
            let arg = literal.parse::<Worry>()?;
            Box::new(move |x| x * arg)
        }
        (literal, "+", "old") => {
            let arg = literal.parse::<Worry>()?;
            Box::new(move |x| arg + x)
        }
        (literal, "+", other) => {
            let a = literal.parse::<Worry>()?;
            let b = other.parse::<Worry>()?;
            Box::new(move |_| a + b)
        }
        (literal, "*", "old") => {
            let arg: Worry = literal.parse::<Worry>()?;
            Box::new(move |x| arg * x)
        }
        (literal, "*", other) => {
            let a = literal.parse::<Worry>()?;
            let b = other.parse::<Worry>()?;
            Box::new(move |_| a * b)
        }
        _ => {
            return Err(Error::Parse(s.into()));
        }
    };
    Ok(closure)
}

fn parse_predicate(s: &str) -> Result<(Worry, Predicate)> {
    let re = regex!(r"^\s*Test: divisible by (?P<divisor>\d+)");
    let caps = re.captures(s).ok_or_else(|| Error::Parse(s.into()))?;
    let m = caps["divisor"].parse::<Worry>()?;
    Ok((m, Box::new(move |x| x % m == 0)))
}

fn parse_send_to(first_line: &str, second_line: &str) -> Result<[usize; 2]> {
    let if_true = regex!(r"^\s*If true: throw to monkey (?P<if_true>\d+)");
    let caps = if_true
        .captures(first_line)
        .ok_or_else(|| Error::Parse(first_line.into()))?;
    let send_to_true = caps["if_true"].parse::<usize>()?;
    let if_false = regex!(r"^\s*If false: throw to monkey (?P<if_false>\d+)");
    let caps = if_false
        .captures(second_line)
        .ok_or_else(|| Error::Parse(second_line.into()))?;
    let send_to_false = caps["if_false"].parse::<usize>()?;
    Ok([send_to_false, send_to_true])
}

/// Reads the next line of input.
fn next_line<'a, L>(mut lines: L) -> Result<&'a str>
where
    L: Iterator<Item = &'a str>,
{
    let line = lines.next().ok_or(Error::UnexpectedEndOfInput)?;
    Ok(line)
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    fn items_to_vecs(monkeys: &[Monkey]) -> Vec<Vec<Worry>> {
        let mut vecs = Vec::new();
        for monkey in monkeys {
            let items: Vec<_> = monkey.items().collect();
            vecs.push(items);
        }
        vecs
    }

    #[test]
    fn test_parse_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let monkeys = parse_input(&input)?;
        let current_items = items_to_vecs(&monkeys);
        assert_eq!(
            current_items,
            vec![
                vec![79, 98],
                vec![54, 65, 75, 74],
                vec![79, 60, 97],
                vec![74],
            ]
        );
        Ok(())
    }

    #[test]
    fn test_round1_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let mut monkeys = parse_input(&input)?;
        do_round(&mut monkeys, |x| x / 3);
        let current_items = items_to_vecs(&monkeys);
        assert_eq!(
            current_items,
            vec![
                vec![20, 23, 27, 26],
                vec![2080, 25, 167, 207, 401, 1046],
                vec![],
                vec![],
            ]
        );
        Ok(())
    }

    #[test]
    fn test_round2_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let mut monkeys = parse_input(&input)?;
        do_round(&mut monkeys, |x| x / 3);
        do_round(&mut monkeys, |x| x / 3);
        let current_items = items_to_vecs(&monkeys);
        assert_eq!(
            current_items,
            vec![
                vec![695, 10, 71, 135, 350],
                vec![43, 49, 58, 55, 362],
                vec![],
                vec![],
            ]
        );
        Ok(())
    }

    #[test]
    fn test_round6_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let mut monkeys = parse_input(&input)?;
        do_round(&mut monkeys, |x| x / 3);
        do_round(&mut monkeys, |x| x / 3);
        do_round(&mut monkeys, |x| x / 3);
        do_round(&mut monkeys, |x| x / 3);
        do_round(&mut monkeys, |x| x / 3);
        do_round(&mut monkeys, |x| x / 3);
        let current_items = items_to_vecs(&monkeys);
        assert_eq!(
            current_items,
            vec![
                vec![8, 70, 176, 26, 34],
                vec![481, 32, 36, 186, 2190],
                vec![],
                vec![],
            ]
        );
        Ok(())
    }

    #[test]
    fn test_round20_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let mut monkeys = parse_input(&input)?;
        for _ in 0..20 {
            do_round(&mut monkeys, |x| x / 3);
        }
        let current_items = items_to_vecs(&monkeys);
        assert_eq!(
            current_items,
            vec![
                vec![10, 12, 14, 26, 34],
                vec![245, 93, 53, 199, 115],
                vec![],
                vec![],
            ]
        );
        Ok(())
    }

    #[test]
    fn test_part1_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let mut monkeys = parse_input(&input)?;
        let ans = solve_part1(&mut monkeys);
        assert_eq!(ans, 10605);
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let mut monkeys = parse_input(&input)?;
        let ans = solve_part1(&mut monkeys);
        assert_eq!(ans, 99840);
        Ok(())
    }

    #[test]
    fn test_part2_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let mut monkeys = parse_input(&input)?;
        let ans = solve_part2(&mut monkeys);
        assert_eq!(ans, 2713310158);
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let mut monkeys = parse_input(&input)?;
        let ans = solve_part2(&mut monkeys);
        assert_eq!(ans, 20683044837);
        Ok(())
    }
}
