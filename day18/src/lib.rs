//! Solutions to [Advent of Code 2022 Day 18](https://adventofcode.com/2022/day/18).

use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::io;
use std::num::ParseIntError;
use std::str::FromStr;

use ndarray::{Array3, ArrayViewMut3};
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
            .map(|x| x.parse::<T>().map_err(Into::into))
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

/// Parses input into a vector of cubes.
///
/// # Errors
///
/// Returns [`Error::Dimension`] if there are not exactly three integer coordinates per line.
/// Returns [`Error::ParseInt`] if there was an error parsing an integer.
pub fn parse_input<T, E>(s: &str) -> Result<Vec<Cube<T>>>
where
    T: FromStr<Err = E>,
    E: Into<Error>,
{
    s.lines().map(str::parse).collect()
}

type Face<T> = (T, T, T);

fn boundary_faces<I>(cubes: I) -> (HashSet<Face<u8>>, HashSet<Face<u8>>, HashSet<Face<u8>>)
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

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
enum CubeKind {
    Exterior,
    Lava,
    Interior,
}

fn mark_cubes<I>(lava: I) -> Array3<CubeKind>
where
    I: IntoIterator<Item = Cube<u8>>,
{
    let lava: HashSet<_> = lava.into_iter().collect();
    let xlimit = 2 + lava.iter().map(|cube| cube.x).max().unwrap_or(0) as usize;
    let ylimit = 2 + lava.iter().map(|cube| cube.y).max().unwrap_or(0) as usize;
    let zlimit = 2 + lava.iter().map(|cube| cube.z).max().unwrap_or(0) as usize;

    let mut array: Array3<Option<CubeKind>> = Array3::default((xlimit, ylimit, zlimit));

    // Mark the lava cubes.
    for cube in &lava {
        let x = cube.x as usize;
        let y = cube.y as usize;
        let z = cube.z as usize;
        array[[x, y, z]] = Some(CubeKind::Lava);
    }

    // Mark the outermost exterior cells.
    initialize_boundary(&mut array.view_mut());

    while update_exterior(&mut array.view_mut()) > 0 {}

    let shape = array.raw_dim();
    let data = array
        .into_iter()
        .map(|opt| opt.unwrap_or(CubeKind::Interior))
        .collect();
    Array3::from_shape_vec(shape, data).expect("the data can fit the shape")
}

fn update_exterior(array: &mut ArrayViewMut3<Option<CubeKind>>) -> usize {
    let shape = array.shape();
    let xlimit = shape[0];
    let ylimit = shape[1];
    let zlimit = shape[2];

    let mut updated = 0;
    for x in 1..xlimit {
        for y in 0..ylimit {
            for z in 0..zlimit {
                if array[[x, y, z]].is_none()
                    && matches!(array[[x - 1, y, z]], Some(CubeKind::Exterior))
                {
                    array[[x, y, z]] = Some(CubeKind::Exterior);
                    updated += 1;
                }
            }
        }
    }
    for x in (0..xlimit - 1).rev() {
        for y in 0..ylimit {
            for z in 0..zlimit {
                if array[[x, y, z]].is_none()
                    && matches!(array[[x + 1, y, z]], Some(CubeKind::Exterior))
                {
                    array[[x, y, z]] = Some(CubeKind::Exterior);
                    updated += 1;
                }
            }
        }
    }
    for y in 1..ylimit {
        for x in 0..ylimit {
            for z in 0..zlimit {
                if array[[x, y, z]].is_none()
                    && matches!(array[[x, y - 1, z]], Some(CubeKind::Exterior))
                {
                    array[[x, y, z]] = Some(CubeKind::Exterior);
                    updated += 1;
                }
            }
        }
    }
    for y in (0..ylimit - 1).rev() {
        for x in 0..xlimit {
            for z in 0..zlimit {
                if array[[x, y, z]].is_none()
                    && matches!(array[[x, y + 1, z]], Some(CubeKind::Exterior))
                {
                    array[[x, y, z]] = Some(CubeKind::Exterior);
                    updated += 1;
                }
            }
        }
    }
    for z in 1..zlimit {
        for x in 0..xlimit {
            for y in 0..ylimit {
                if array[[x, y, z]].is_none()
                    && matches!(array[[x, y, z - 1]], Some(CubeKind::Exterior))
                {
                    array[[x, y, z]] = Some(CubeKind::Exterior);
                    updated += 1;
                }
            }
        }
    }
    for z in (0..zlimit - 1).rev() {
        for x in 0..xlimit {
            for y in 0..ylimit {
                if array[[x, y, z]].is_none()
                    && matches!(array[[x, y, z + 1]], Some(CubeKind::Exterior))
                {
                    array[[x, y, z]] = Some(CubeKind::Exterior);
                    updated += 1;
                }
            }
        }
    }
    updated
}

fn initialize_boundary(array: &mut ArrayViewMut3<Option<CubeKind>>) {
    let shape = array.shape();
    let xlimit = shape[0];
    let ylimit = shape[1];
    let zlimit = shape[2];

    // Mark the boundary
    // yz planes
    for y in 0..ylimit {
        for z in 0..zlimit {
            array[[0, y, z]] = Some(CubeKind::Exterior);
            array[[xlimit - 1, y, z]] = Some(CubeKind::Exterior);
        }
    }

    // xz planes
    for x in 0..xlimit {
        for z in 0..zlimit {
            array[[x, 0, z]] = Some(CubeKind::Exterior);
            array[[x, ylimit - 1, z]] = Some(CubeKind::Exterior);
        }
    }

    // xy planes
    for x in 0..xlimit {
        for y in 0..ylimit {
            array[[x, y, 0]] = Some(CubeKind::Exterior);
            array[[x, y, zlimit - 1]] = Some(CubeKind::Exterior);
        }
    }
}

pub fn solve_part2<I>(cubes: I) -> usize
where
    I: IntoIterator<Item = Cube<u8>>,
{
    let cubes: Vec<_> = cubes.into_iter().collect();
    let array = mark_cubes(cubes.clone());
    let mut interior = Vec::new();
    let shape = array.shape();
    let xlimit = shape[0];
    let ylimit = shape[1];
    let zlimit = shape[2];
    for x in 0..xlimit {
        for y in 0..ylimit {
            for z in 0..zlimit {
                if matches!(array[[x, y, z]], CubeKind::Interior) {
                    interior.push(Cube::new(x as u8, y as u8, z as u8));
                }
            }
        }
    }
    let boundary_faces = solve_part1(cubes);
    let interior_boundary_faces = solve_part1(interior);
    boundary_faces - interior_boundary_faces
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
        assert_eq!(surface_area, 2428);
        Ok(())
    }
}
