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
    #[inline]
    pub fn shape(&self) -> [usize; 2] {
        self.shape
    }

    #[must_use]
    pub fn get(&self, idx: [usize; 2]) -> Option<&T> {
        let index = self.index(idx)?;
        self.data.get(index)
    }

    /// Returns an interator over the `i`th row of the grid.
    ///
    /// # Panics
    ///
    /// Panics if `i` is greater than or equal to the number of rows.
    pub fn row(&self, i: usize) -> impl Iterator<Item = &T> {
        let num_cols = self.shape[1];
        let idx = self.index([i, 0]).unwrap();
        self.data[idx..idx + num_cols].iter()
    }

    /// Returns an interator over the `j`th column of the grid.
    ///
    /// # Panics
    ///
    /// Panics if `j` is greater than or equal to the number of columns.
    pub fn column(&self, j: usize) -> impl Iterator<Item = &T> {
        let num_rows = self.shape[0];
        let num_cols = self.shape[1];
        (j..j + num_rows)
            .step_by(num_cols)
            .map(|idx| &self.data[idx])
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

impl<T: Default> Grid<T> {
    #[must_use]
    pub fn from_shape_default(shape: [usize; 2]) -> Self {
        let data = (0..shape[0] * shape[1]).map(|_| T::default()).collect();
        Self { shape, data }
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
