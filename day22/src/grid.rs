use std::ops::{Index, IndexMut};

use thiserror::Error;

/// A two-dimensional array.
pub struct Grid<T> {
    shape: [usize; 2],
    data: Vec<T>,
}

/// The error type for operations in this crate.
#[derive(Debug, Error)]
pub enum Error {
    /// An error in the shape of the grid.
    #[error("Error in shape of grid")]
    Shape,
}

impl<T> Grid<T> {
    /// Creates a new grid having the given number of columns.
    #[must_use]
    pub fn new(num_cols: usize) -> Self {
        Self {
            shape: [0, num_cols],
            data: Vec::new(),
        }
    }

    /// Creates a new grid of the given shape from a vector of data.
    ///
    /// # Errors
    ///
    /// Returns an error if the data cannot be viewed as a grid of the specified shape.
    pub fn from_shape_vec(shape: [usize; 2], data: Vec<T>) -> Result<Self, Error> {
        let size = shape[0] * shape[1];
        if size == data.len() {
            Ok(Self { shape, data })
        } else {
            Err(Error::Shape)
        }
    }

    /// Pushes a new row onto the grid.
    ///
    /// # Errors
    ///
    /// Returns [`Error::Shape`] if the row does not have the correct length.
    pub fn push_row(&mut self, row: Vec<T>) -> Result<(), Error> {
        if row.len() == self.shape[1] {
            self.shape[0] += 1;
            self.data.extend(row);
            Ok(())
        } else {
            Err(Error::Shape)
        }
    }

    #[must_use]
    #[inline]
    pub fn num_rows(&self) -> usize {
        self.shape[0]
    }

    #[must_use]
    #[inline]
    pub fn num_cols(&self) -> usize {
        self.shape[1]
    }

    #[must_use]
    pub fn get(&self, idx: [usize; 2]) -> Option<&T> {
        let index = self.index(idx)?;
        self.data.get(index)
    }

    #[must_use]
    #[inline]
    fn index(&self, idx: [usize; 2]) -> Option<usize> {
        let i = idx[0];
        let j = idx[1];
        if i <= self.num_rows() && j <= self.num_cols() {
            Some(i * self.num_cols() + j)
        } else {
            None
        }
    }
}

impl<T> Index<[usize; 2]> for Grid<T> {
    type Output = T;

    /// # Panics
    ///
    /// Panics if `idx[0]` is greater than the number of rows or if `idx[1]` is greater than the
    /// number of columns.
    fn index(&self, idx: [usize; 2]) -> &Self::Output {
        let index = self.index(idx).unwrap();
        &self.data[index]
    }
}

impl<T> IndexMut<[usize; 2]> for Grid<T> {
    /// # Panics
    ///
    /// Panics if `idx[0]` is greater than the number of rows or if `idx[1]` is greater than the
    /// number of columns.
    fn index_mut(&mut self, idx: [usize; 2]) -> &mut Self::Output {
        let index = self.index(idx).unwrap();
        &mut self.data[index]
    }
}
