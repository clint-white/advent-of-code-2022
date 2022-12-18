//! Solutions to [Advent of Code 2022 Day 15](https://adventofcode.com/2022/day/15).

use std::collections::HashSet;
use std::io;
use std::num::ParseIntError;
use std::ops::RangeInclusive;
use std::str::FromStr;

use num_traits::Signed;
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

    /// An error parsing a sensor report.
    #[error("Parse error")]
    ParseSensorReport(String),

    /// An error parsing an integer.
    #[error("Error parsing an integer")]
    ParseInt(#[from] ParseIntError),

    /// No location possible for beacon.
    #[error("No location possible for beacon")]
    NoLocation,

    /// Multiple locations possible for beacon.
    #[error("Multiple locations possible for beacon")]
    MultipleLocations,
}

/// A specialized [`Result`] type for operations in this crate.
///
/// [`Result`]: std::result::Result
pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Point<T> {
    pub x: T,
    pub y: T,
}

impl<T> Point<T> {
    pub fn new(x: T, y: T) -> Self {
        Self { x, y }
    }
}

impl<T> Point<T>
where
    T: Signed + Ord + Copy,
{
    pub fn manhatten_distance(&self, other: &Self) -> T {
        (self.x - other.x).abs() + (self.y - other.y).abs()
    }
}

#[derive(Debug, Copy, Clone)]
pub struct SensorReport<T> {
    sensor: Point<T>,
    beacon: Point<T>,
}

impl<T: Copy> SensorReport<T> {
    pub fn sensor(&self) -> Point<T> {
        self.sensor
    }

    pub fn beacon(&self) -> Point<T> {
        self.beacon
    }
}

impl FromStr for SensorReport<i64> {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        let re = regex!(
            r"Sensor at x=(?P<sx>-?\d+), y=(?P<sy>-?\d+): closest beacon is at x=(?P<bx>-?\d+), y=(?P<by>-?\d+)"
        );
        let captures = re
            .captures(s)
            .ok_or_else(|| Error::ParseSensorReport(s.into()))?;
        let sensor_x = captures["sx"].parse()?;
        let sensor_y = captures["sy"].parse()?;
        let beacon_x = captures["bx"].parse()?;
        let beacon_y = captures["by"].parse()?;
        let sensor = Point::new(sensor_x, sensor_y);
        let beacon = Point::new(beacon_x, beacon_y);
        let report = Self { sensor, beacon };
        Ok(report)
    }
}

impl<T> SensorReport<T>
where
    T: Signed + Ord + Copy,
{
    pub fn radius(&self) -> T {
        self.sensor.manhatten_distance(&self.beacon)
    }
}

pub fn parse_input(s: &str) -> Result<Vec<SensorReport<i64>>> {
    s.lines().map(str::parse).collect()
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ClosedInterval<Idx> {
    start: Idx,
    end: Idx,
}

impl<Idx> ClosedInterval<Idx> {
    pub fn new(start: Idx, end: Idx) -> Self {
        Self { start, end }
    }

    pub fn start(&self) -> &Idx {
        &self.start
    }

    pub fn end(&self) -> &Idx {
        &self.end
    }
}

impl<Idx: PartialOrd> ClosedInterval<Idx> {
    /// Returns `true` iff the interval is empty.
    pub fn is_empty(&self) -> bool {
        self.end < self.start
    }

    /// Returns `true` iff `self` and `other` have nonempty intersection.
    pub fn intersects(&self, other: &Self) -> bool {
        self.start <= other.end && other.start <= self.end
    }

    pub fn contains(&self, item: &Idx) -> bool {
        &self.start <= item && item <= &self.end
    }
}

impl<Idx> ClosedInterval<Idx>
where
    Idx: Copy + Ord + Signed,
{
    pub fn intersection(&self, other: &Self) -> Option<Self> {
        let start = self.start.max(other.start);
        let end = self.end.min(other.end);
        if start <= end {
            Some(Self::new(start, end))
        } else {
            None
        }
    }
}

impl ClosedInterval<i64> {
    #[must_use]
    pub fn len(&self) -> usize {
        0.max(self.end - self.start + 1) as usize
    }

    /// Returns the union of `self` and `other` if it forms a single closed interval.
    #[must_use]
    pub fn union(&self, other: &Self) -> Option<Self> {
        if self.end.min(other.end) + 1 >= self.start.max(other.start) {
            Some(Self::new(
                self.start.min(other.start),
                self.end.max(other.end),
            ))
        } else {
            None
        }
    }
}

impl IntoIterator for ClosedInterval<i64> {
    type Item = i64;
    type IntoIter = RangeInclusive<i64>;

    fn into_iter(self) -> Self::IntoIter {
        self.start..=self.end
    }
}

#[must_use]
pub fn build_intervals(reports: &[SensorReport<i64>], y: i64) -> Vec<ClosedInterval<i64>> {
    reports
        .iter()
        .filter_map(|report| {
            let sensor = report.sensor();
            let radius = report.radius();
            let d = (sensor.y - y).abs();
            if radius >= d {
                Some(ClosedInterval::new(
                    sensor.x - (radius - d),
                    sensor.x + (radius - d),
                ))
            } else {
                None
            }
        })
        .collect()
}

#[must_use]
pub fn merge_intervals(mut intervals: Vec<ClosedInterval<i64>>) -> Vec<ClosedInterval<i64>> {
    intervals.sort_unstable();
    let mut merged = Vec::new();
    let mut intervals = intervals.into_iter();
    if let Some(mut i) = intervals.next() {
        for j in intervals {
            if let Some(union) = i.union(&j) {
                i = union;
            } else {
                merged.push(i);
                i = j;
            }
        }
        merged.push(i);
    }
    merged
}

pub fn solve_part1(reports: &[SensorReport<i64>], y: i64) -> usize {
    // Find the beacon positions.
    let beacon_xs: HashSet<_> = reports
        .iter()
        .filter_map(|report| {
            if report.beacon().y == y {
                Some(report.beacon().x)
            } else {
                None
            }
        })
        .collect();

    let intervals = merge_intervals(build_intervals(reports, y));
    let mut non_beacons = intervals.iter().map(ClosedInterval::len).sum();
    non_beacons -= beacon_xs
        .iter()
        .filter(|x| intervals.iter().any(|i| i.contains(x)))
        .count();
    non_beacons
}

pub fn solve_part2(
    reports: &[SensorReport<i64>],
    xrange: RangeInclusive<i64>,
    yrange: RangeInclusive<i64>,
) -> Result<i64> {
    let mut ans = Err(Error::NoLocation);
    for y in yrange {
        let intervals = merge_intervals(build_intervals(reports, y));
        match intervals.len() {
            1 => {
                if intervals[0].start() > xrange.start() || intervals[0].end() < xrange.end() {
                    return Err(Error::MultipleLocations);
                }
            }
            2 => {
                if ans.is_err()
                    && intervals[0].start() <= xrange.start()
                    && intervals[0].end() + 2 == *intervals[1].start()
                    && intervals[1].end() >= xrange.end()
                {
                    let x = *intervals[0].end() + 1;
                    ans = Ok(x * 4_000_000 + y);
                } else {
                    return Err(Error::MultipleLocations);
                }
            }
            _ => {
                return Err(Error::MultipleLocations);
            }
        }
    }
    ans
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_part1_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let reports = parse_input(&input)?;
        let num = solve_part1(&reports, 10);
        assert_eq!(num, 26);
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let reports = parse_input(&input)?;
        let num = solve_part1(&reports, 2_000_000);
        assert_eq!(num, 4811413);
        Ok(())
    }

    #[test]
    fn test_part2_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let reports = parse_input(&input)?;
        let num = solve_part2(&reports, 0..=20, 0..=20)?;
        assert_eq!(num, 56000011);
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let reports = parse_input(&input)?;
        let num = solve_part2(&reports, 0..=4_000_000, 0..=4_000_000)?;
        assert_eq!(num, 13171855019123);
        Ok(())
    }
}
