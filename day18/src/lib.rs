//! Solutions to [Advent of Code 2022 Day 18](https://adventofcode.com/2022/day/18).

use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;
use std::io;
use std::num::ParseIntError;
use std::str::FromStr;

use thiserror::Error;

/// The error type for operations in this crate.
#[derive(Debug, Error)]
pub enum Error {
    /// An underlying [`io::Error`].
    #[error("I/O error")]
    Io(#[from] io::Error),

    /// Incorrect number of coordinates.
    #[error("Incorrect dimension: got {0} coordinates, expected 3")]
    Dimension(usize),

    /// Error parsing an integer.
    #[error("Error parsing expected integer")]
    ParseInt(#[from] ParseIntError),
}

/// A specialized [`Result`] type for operations in this crate.
///
/// [`Result`]: std::result::Result
pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Cube<T> {
    x: T,
    y: T,
    z: T,
}

impl<T> Cube<T> {
    pub fn new(x: T, y: T, z: T) -> Self {
        Self { x, y, z }
    }
}

impl<T, E> FromStr for Cube<T>
where
    T: FromStr<Err = E>,
    E: Into<Error>,
{
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        let result: Result<Vec<_>> = s
            .split(',')
            .map(|x| x.parse::<T>().map_err(|e| e.into()))
            .collect();
        let mut coordinates = result?;
        let z = coordinates
            .pop()
            .ok_or_else(|| Error::Dimension(coordinates.len()))?;
        let y = coordinates
            .pop()
            .ok_or_else(|| Error::Dimension(coordinates.len()))?;
        let x = coordinates
            .pop()
            .ok_or_else(|| Error::Dimension(coordinates.len()))?;
        let cube = Cube::new(x, y, z);
        Ok(cube)
    }
}

pub fn parse_input<T, E>(s: &str) -> Result<Vec<Cube<T>>>
where
    T: FromStr<Err = E>,
    E: Into<Error>,
{
    s.lines().map(str::parse).collect()
}

pub type Face<T> = (T, T, T);

pub fn boundary_faces<I>(cubes: I) -> (HashSet<Face<u8>>, HashSet<Face<u8>>, HashSet<Face<u8>>)
where
    I: IntoIterator<Item = Cube<u8>>,
{
    let mut faces_yz = HashMap::new();
    let mut faces_xz = HashMap::new();
    let mut faces_xy = HashMap::new();
    for cube in cubes {
        *faces_yz.entry((cube.x, cube.y, cube.z)).or_insert(0) += 1;
        *faces_yz.entry((cube.x + 1, cube.y, cube.z)).or_insert(0) += 1;
        *faces_xz.entry((cube.x, cube.y, cube.z)).or_insert(0) += 1;
        *faces_xz.entry((cube.x, cube.y + 1, cube.z)).or_insert(0) += 1;
        *faces_xy.entry((cube.x, cube.y, cube.z)).or_insert(0) += 1;
        *faces_xy.entry((cube.x, cube.y, cube.z + 1)).or_insert(0) += 1;
    }
    assert!(faces_yz.values().all(|&count| count == 1 || count == 2));
    assert!(faces_xz.values().all(|&count| count == 1 || count == 2));
    assert!(faces_xy.values().all(|&count| count == 1 || count == 2));
    let boundary_yz = faces_yz
        .into_iter()
        .filter_map(|(key, value)| if value == 1 { Some(key) } else { None })
        .collect();
    let boundary_xz = faces_xz
        .into_iter()
        .filter_map(|(key, value)| if value == 1 { Some(key) } else { None })
        .collect();
    let boundary_xy = faces_xy
        .into_iter()
        .filter_map(|(key, value)| if value == 1 { Some(key) } else { None })
        .collect();
    (boundary_yz, boundary_xz, boundary_xy)
}

pub fn solve_part1<I>(cubes: I) -> usize
where
    I: IntoIterator<Item = Cube<u8>>,
{
    let (faces_yz, faces_xz, faces_xy) = boundary_faces(cubes);
    faces_yz.len() + faces_xz.len() + faces_xy.len()
}

pub fn external_cubes<I>(cubes: I) -> HashSet<Cube<u8>>
where
    I: IntoIterator<Item = Cube<u8>>,
{
    let cubes: HashSet<_> = cubes.into_iter().collect();
    let endx = 2 + cubes.iter().map(|cube| cube.x).max().unwrap_or(0);
    let endy = 2 + cubes.iter().map(|cube| cube.y).max().unwrap_or(0);
    let endz = 2 + cubes.iter().map(|cube| cube.z).max().unwrap_or(0);

    let mut visited = HashSet::new();
    let mut queue = VecDeque::new();
    queue.push_back(Cube::<u8>::new(0, 0, 0));
    while let Some(cube) = queue.pop_front() {
        visited.insert(cube);
        if let Some(x1) = cube.x.checked_sub(1) {
            let neighbor = Cube::new(x1, cube.y, cube.z);
            if !cubes.contains(&neighbor) && !visited.contains(&neighbor) {
                queue.push_back(neighbor);
            }
        }
        if cube.x < endx {
            let neighbor = Cube::new(cube.x + 1, cube.y, cube.z);
            if !cubes.contains(&neighbor) && !visited.contains(&neighbor) {
                queue.push_back(neighbor);
            }
        }
        if let Some(y1) = cube.y.checked_sub(1) {
            let neighbor = Cube::new(cube.x, y1, cube.z);
            if !cubes.contains(&neighbor) && !visited.contains(&neighbor) {
                queue.push_back(neighbor);
            }
        }
        if cube.y < endy {
            let neighbor = Cube::new(cube.x, cube.y + 1, cube.z);
            if !cubes.contains(&neighbor) && !visited.contains(&neighbor) {
                queue.push_back(neighbor);
            }
        }
        if let Some(z1) = cube.z.checked_sub(1) {
            let neighbor = Cube::new(cube.x, cube.y, z1);
            if !cubes.contains(&neighbor) && !visited.contains(&neighbor) {
                queue.push_back(neighbor);
            }
        }
        if cube.z < endz {
            let neighbor = Cube::new(cube.x, cube.y, cube.z + 1);
            if !cubes.contains(&neighbor) && !visited.contains(&neighbor) {
                queue.push_back(neighbor);
            }
        }
    }
    visited
}

pub fn solve_part2<I>(cubes: I) -> usize
where
    I: IntoIterator<Item = Cube<u8>>,
{
    let cubes: Vec<_> = cubes.into_iter().collect();
    let exterior_cubes = external_cubes(cubes.clone());
    let (ext_boundary_yz, ext_boundary_xz, ext_boundary_xy) = boundary_faces(exterior_cubes);
    let (boundary_yz, boundary_xz, boundary_xy) = boundary_faces(cubes);
    boundary_yz.intersection(&ext_boundary_yz).count()
        + boundary_xz.intersection(&ext_boundary_xz).count()
        + boundary_xy.intersection(&ext_boundary_xy).count()
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_part1_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let cubes = parse_input(&input)?;
        let surface_area = solve_part1(cubes);
        assert_eq!(surface_area, 64);
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let cubes = parse_input(&input)?;
        let surface_area = solve_part1(cubes);
        assert_eq!(surface_area, 4242);
        Ok(())
    }

    #[test]
    fn test_part2_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let cubes = parse_input(&input)?;
        let surface_area = solve_part2(cubes);
        assert_eq!(surface_area, 58);
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let cubes = parse_input(&input)?;
        let surface_area = solve_part2(cubes);
        assert_eq!(surface_area, 4242);
        Ok(())
    }
}
