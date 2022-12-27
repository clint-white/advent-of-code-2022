//! Solutions to [Advent of Code 2022 Day 18](https://adventofcode.com/2022/day/18).

use std::collections::HashSet;
use std::hash::Hash;
use std::io;
use std::num::ParseIntError;
use std::str::FromStr;

use ndarray::{s, Array3, ArrayViewMut1, ArrayViewMut3, Axis};
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

/// Returns the number of cube faces which are not shared with another cube.
pub fn count_boundary_faces(cubes: &[Cube<usize>]) -> usize {
    // Remove any duplicate cubes so that we can assert that any face belongs to at most two cubes
    // in the sample.
    let cubes: HashSet<_> = cubes.iter().copied().collect();

    let xlimit = 2 + cubes.iter().map(|cube| cube.x).max().unwrap_or(0);
    let ylimit = 2 + cubes.iter().map(|cube| cube.y).max().unwrap_or(0);
    let zlimit = 2 + cubes.iter().map(|cube| cube.z).max().unwrap_or(0);

    let mut faces_yz: Array3<usize> = Array3::default((xlimit, ylimit, zlimit));
    let mut faces_xz: Array3<usize> = Array3::default((xlimit, ylimit, zlimit));
    let mut faces_xy: Array3<usize> = Array3::default((xlimit, ylimit, zlimit));

    for cube in &cubes {
        faces_yz[[cube.x, cube.y, cube.z]] += 1;
        faces_yz[[cube.x + 1, cube.y, cube.z]] += 1;
        faces_xz[[cube.x, cube.y, cube.z]] += 1;
        faces_xz[[cube.x, cube.y + 1, cube.z]] += 1;
        faces_xy[[cube.x, cube.y, cube.z]] += 1;
        faces_xy[[cube.x, cube.y, cube.z + 1]] += 1;
    }
    // Each face can belong to at most two cubes as long as the cubes are unique.
    assert!(faces_yz.iter().all(|&count| count <= 2));
    assert!(faces_xz.iter().all(|&count| count <= 2));
    assert!(faces_xy.iter().all(|&count| count <= 2));

    // Count the number of faces that occur exactly once.
    let boundary_yz = faces_yz.iter().filter(|&&count| count == 1).count();
    let boundary_xz = faces_xz.iter().filter(|&&count| count == 1).count();
    let boundary_xy = faces_xy.iter().filter(|&&count| count == 1).count();
    boundary_yz + boundary_xz + boundary_xy
}

pub fn solve_part1(cubes: &[Cube<usize>]) -> usize {
    count_boundary_faces(cubes)
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
enum CubeKind {
    Exterior,
    Lava,
    Interior,
}

/// Labels each element of the array bounding the cubelets according to its component class.
fn label_cube_kinds(lava: &[Cube<usize>]) -> Array3<CubeKind> {
    let xlimit = 2 + lava.iter().map(|cube| cube.x).max().unwrap_or(0);
    let ylimit = 2 + lava.iter().map(|cube| cube.y).max().unwrap_or(0);
    let zlimit = 2 + lava.iter().map(|cube| cube.z).max().unwrap_or(0);

    let mut array: Array3<Option<CubeKind>> = Array3::default((xlimit, ylimit, zlimit));

    // Mark the lava cubes.
    for cube in lava.iter() {
        array[[cube.x, cube.y, cube.z]] = Some(CubeKind::Lava);
    }

    // Identify the exterior cubes by initializing the boundary of a box which completely encloses
    // lava cubes, and the iteratively extending the exterior label to neighbors of exterior cells.
    let mut view = array.view_mut();
    initialize_exterior(&mut view);
    while update_exterior(&mut view) > 0 {}

    // Any cell not marked at this point is necessarily an interior cell.
    let shape = array.raw_dim();
    let data = array
        .into_iter()
        .map(|opt| opt.unwrap_or(CubeKind::Interior))
        .collect();
    Array3::from_shape_vec(shape, data).expect("the data can fit the shape")
}

/// Marks the first and last planes along each axis of the array as [`CubeKind::Exterior`].
fn initialize_exterior(array: &mut ArrayViewMut3<Option<CubeKind>>) {
    let (mut first, mut last) = array.multi_slice_mut((s![0, .., ..], s![-1, .., ..]));
    first.fill(Some(CubeKind::Exterior));
    last.fill(Some(CubeKind::Exterior));

    let (mut first, mut last) = array.multi_slice_mut((s![.., 0, ..], s![.., -1, ..]));
    first.fill(Some(CubeKind::Exterior));
    last.fill(Some(CubeKind::Exterior));

    let (mut first, mut last) = array.multi_slice_mut((s![.., .., 0], s![.., .., -1]));
    first.fill(Some(CubeKind::Exterior));
    last.fill(Some(CubeKind::Exterior));
}

/// Marks array elements adjacent to an exterior element along any axis as also exterior.
fn update_exterior(array: &mut ArrayViewMut3<Option<CubeKind>>) -> usize {
    let mut updated = 0;

    // For each of the axes of the array, stride along each lane of that axis both forwards and
    // backwards propogating [`CellKind::Exterior`] labels from a cell to its successor in the
    // direction of stride.
    array.lanes_mut(Axis(0)).into_iter().for_each(|mut lane| {
        updated += update_lane(lane.view_mut());
        updated += update_lane(lane.slice_mut(s![..; -1]));
    });
    array.lanes_mut(Axis(1)).into_iter().for_each(|mut lane| {
        updated += update_lane(lane.view_mut());
        updated += update_lane(lane.slice_mut(s![..; -1]));
    });
    array.lanes_mut(Axis(2)).into_iter().for_each(|mut lane| {
        updated += update_lane(lane.view_mut());
        updated += update_lane(lane.slice_mut(s![..; -1]));
    });
    updated
}

/// Extends exterior cells along a 1-D lane of the array.
///
/// If a cell's predecessor in the direction of stride is an exterior cell, and the current cell is
/// unknown (`None`), marks the current cell as also exterior.
fn update_lane(mut array: ArrayViewMut1<Option<CubeKind>>) -> usize {
    let mut updated = 0;
    // Use `.cell_view()` to get interior mutability since `.windows()` takes only a shared
    // reference.
    array.cell_view().windows([2]).into_iter().for_each(|w| {
        if w[1].get().is_none() && matches!(w[0].get(), Some(CubeKind::Exterior)) {
            w[1].set(Some(CubeKind::Exterior));
            updated += 1;
        }
    });
    updated
}

pub fn solve_part2(lava: &[Cube<usize>]) -> usize {
    // 1. Find the interior cubes.
    let labels = label_cube_kinds(lava);
    let interior: Vec<_> = labels
        .indexed_iter()
        .filter_map(|(dim, elt)| {
            if matches!(elt, CubeKind::Interior) {
                Some(Cube::new(dim.0, dim.1, dim.2))
            } else {
                None
            }
        })
        .collect();
    // 2. Count the boundary of the lava cubes, then subtract the size of the boundary of the
    //    interior cubes.
    let boundary_faces = solve_part1(lava);
    let interior_boundary_faces = solve_part1(&interior);
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
        let surface_area = solve_part1(&cubes);
        assert_eq!(surface_area, 64);
        Ok(())
    }

    #[test]
    fn test_part1_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let cubes = parse_input(&input)?;
        let surface_area = solve_part1(&cubes);
        assert_eq!(surface_area, 4242);
        Ok(())
    }

    #[test]
    fn test_part2_example() -> Result<()> {
        let input = fs::read_to_string("data/example")?;
        let cubes = parse_input(&input)?;
        let surface_area = solve_part2(&cubes);
        assert_eq!(surface_area, 58);
        Ok(())
    }

    #[test]
    fn test_part2_input() -> Result<()> {
        let input = fs::read_to_string("data/input")?;
        let cubes = parse_input(&input)?;
        let surface_area = solve_part2(&cubes);
        assert_eq!(surface_area, 2428);
        Ok(())
    }
}
