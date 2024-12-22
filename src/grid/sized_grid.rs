use crate::coordinate_system::Coordinate;
use crate::grid::iterators::GridIter;
use crate::grid::sized_grid::iterator::GridIterMut;
use crate::grid::{Grid, GridMut};
use std::fmt::{Debug, Formatter};

/// A statically sized grid structure.
///
/// # Type Parameters
///
/// * `T` - The type of elements stored in the grid.
/// * `ROW` - The number of rows in the grid.
/// * `COL` - The number of columns in the grid.
///
/// # Examples
///
/// ```
/// use aoc_utils_rust::grid::Grid;
/// use self::aoc_utils_rust::grid::sized_grid::SizedGrid;
/// use self::aoc_utils_rust::coordinate_system::Coordinate;
///
/// let grid = SizedGrid::<i32, 2, 3>::from([[1, 2, 3], [4, 5, 6]]);
/// assert_eq!(grid.num_rows(), 2);
/// assert_eq!(grid.num_cols(), 3);
/// assert_eq!(grid.get(&Coordinate::new(0, 1)), Some(&2));
/// assert!(grid.is_valid_coordinate(&Coordinate::new(1, 2)));
/// assert!(!grid.is_valid_coordinate(&Coordinate::new(2, 3)));
/// ```
#[repr(transparent)]
#[derive(Clone)]
pub struct SizedGrid<T, const ROW: usize, const COL: usize> {
    pub matrix: [[T; COL]; ROW],
}

impl<T, const ROW: usize, const COL: usize> SizedGrid<T, ROW, COL> {
    /// Creates a new `SizedGrid` from a 2D array.
    ///
    ///
    /// # Arguments
    ///
    /// * `grid` - A 2D array representing the grid.
    ///
    /// # Returns
    ///
    /// A new `SizedGrid` instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::rc::Rc;
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::{Grid, GridMut};
    /// use aoc_utils_rust::grid::sized_grid::SizedGrid;
    ///
    /// #[derive(Clone)]
    /// struct NonCopyType {
    ///     id: u8,
    ///     rc: Rc<()>
    /// }
    ///
    /// let mut grid = SizedGrid::<Option<NonCopyType>, 2, 3>::new(None);
    /// let type_rc = NonCopyType{ id: 1, rc: Rc::new(()) };
    /// *grid.get_mut(&Coordinate::new(0, 0)).unwrap() = Some(type_rc);
    ///
    /// assert_eq!(grid.num_rows(), 2);
    /// assert_eq!(grid.num_cols(), 3);
    ///
    /// if let Some(value) = grid.get(&Coordinate::new(0, 0)) {
    ///     assert_eq!(value.as_ref().unwrap().id, 1);
    /// }else {
    ///     panic!("Expected Some value at (0, 0)");
    /// }
    /// ```
    #[inline(always)]
    pub fn new(default: T) -> Self
    where
        T: Clone,
    {
        // This was done to allow for the creation of a 2D array with non-copy types.
        // [init_with_non_copy_types](https://stackoverflow.com/questions/28656387/initialize-a-large-fixed-size-array-with-non-copy-types)
        Self {
            matrix: std::array::from_fn(|_| std::array::from_fn(|_| default.clone())),
        }
    }

    /// Creates a new `SizedGrid` from a 2D array.
    ///
    /// # Arguments
    ///
    /// * `grid` - A 2D array representing the grid.
    ///
    /// # Returns
    ///
    /// A new `SizedGrid` instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::Grid;
    /// use aoc_utils_rust::grid::sized_grid::SizedGrid;
    ///
    /// let grid = SizedGrid::<i32, 2, 3>::from([[1, 2, 3], [4, 5, 6]]);
    /// assert_eq!(grid.num_rows(), 2);
    /// assert_eq!(grid.num_cols(), 3);
    /// assert_eq!(grid.get(&Coordinate::new(0, 1)), Some(&2));
    /// assert!(grid.is_valid_coordinate(&Coordinate::new(1, 2)));
    /// assert!(!grid.is_valid_coordinate(&Coordinate::new(2, 3)));
    /// ```
    #[inline(always)]
    pub const fn from(grid: [[T; COL]; ROW]) -> Self {
        Self { matrix: grid }
    }

    #[inline(always)]
    pub fn with_size_from<O>(_: &SizedGrid<O, ROW, COL>, default: T) -> Self
    where
        T: Clone,
    {
        Self {
            matrix: std::array::from_fn(|_| std::array::from_fn(|_| default.clone())),
        }
    }

    #[inline(always)]
    pub const fn get(&self, position: &Coordinate) -> Option<&T> {
        if self.is_valid_coordinate(position) {
            Some(&self.matrix[position.i as usize][position.j as usize])
        } else {
            None
        }
    }

    /// Returns a reference to the element at the specified position without bounds checking.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not perform bounds checking. The caller must ensure
    /// that the position is within the bounds of the grid.
    ///
    /// # Arguments
    ///
    /// * `position` - The position of the element.
    ///
    /// # Returns
    ///
    /// A reference to the element at the specified position.
    ///
    /// # Panics
    ///
    /// Panics if the position is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::sized_grid::SizedGrid;
    ///
    /// let grid = SizedGrid::<i32, 2, 3>::from([[1, 2, 3], [4, 5, 6]]);
    /// let coordinate = Coordinate::new(0, 1);
    ///
    /// // Safety: We know that the coordinate (0, 1) is within the bounds of the grid.
    /// let value = unsafe { grid.get_unchecked(&coordinate) };
    /// assert_eq!(*value, 2);
    ///
    /// // This will panic because the coordinate is out of bounds.
    /// // let invalid_coordinate = Coordinate::new(3, 3);
    /// // let invalid_value = unsafe { grid.get_unchecked(&invalid_coordinate) };
    /// ```
    #[inline(always)]
    pub const unsafe fn get_unchecked(&self, position: &Coordinate) -> &T {
        &self.matrix[position.i as usize][position.j as usize]
    }

    #[inline(always)]
    pub const fn is_valid_coordinate(&self, coordinate: &Coordinate) -> bool {
        0 <= coordinate.i
            && coordinate.i < ROW as i32
            && 0 <= coordinate.j
            && coordinate.j < COL as i32
    }

    #[inline(always)]
    pub const fn num_rows(&self) -> usize {
        ROW
    }

    #[inline(always)]
    pub const fn num_cols(&self) -> usize {
        COL
    }

    /// Creates a mutable iterator over the grid.
    ///
    /// # Returns
    ///
    /// A `GridIterMut` over the grid.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::sized_grid::SizedGrid;
    /// use aoc_utils_rust::grid::GridMut;
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// let mut grid = SizedGrid::from([[1, 2, 3], [4, 5, 6]]);
    /// let mut iter = grid.iter_mut();
    ///
    /// let mut row_iter = iter.next().unwrap();
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 0), &mut 1)));
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 1), &mut 2)));
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 2), &mut 3)));
    /// assert_eq!(row_iter.next(), None);
    ///
    /// let mut row_iter = iter.next().unwrap();
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(1, 0), &mut 4)));
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(1, 1), &mut 5)));
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(1, 2), &mut 6)));
    /// assert_eq!(row_iter.next(), None);
    ///
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter_mut(&mut self) -> GridIterMut<'_, T, ROW, COL> {
        GridIterMut::new(self)
    }
}

impl<T: Debug, const ROW: usize, const COL: usize> Debug for SizedGrid<T, ROW, COL> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "SizedGrid: (ROW: {} x COL:{}) {{", ROW, COL)?;
        for rows in &self.matrix {
            write!(f, "\t")?;
            for cell in rows.iter() {
                write!(f, "{:?} ", cell)?;
            }
            writeln!(f)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl<T, const ROW: usize, const COL: usize> Grid<T> for SizedGrid<T, ROW, COL> {
    /// Returns the number of rows in the grid.
    ///
    /// # Returns
    ///
    /// The number of rows.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::Grid;
    /// use aoc_utils_rust::grid::sized_grid::SizedGrid;
    ///
    /// let grid = SizedGrid::<i32, 2, 3>::from([[1, 2, 3], [4, 5, 6]]);
    /// assert_eq!(grid.num_rows(), 2);
    /// ```
    #[inline(always)]
    fn num_rows(&self) -> usize {
        self.num_rows()
    }

    /// Returns the number of columns in the grid.
    ///
    /// # Returns
    ///
    /// The number of columns.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::Grid;
    /// use aoc_utils_rust::grid::sized_grid::SizedGrid;
    ///
    /// let grid = SizedGrid::<i32, 2, 3>::from([[1, 2, 3], [4, 5, 6]]);
    /// assert_eq!(grid.num_cols(), 3);
    /// ```
    fn num_cols(&self) -> usize {
        self.num_cols()
    }

    /// Returns a reference to the row at the specified index.
    ///
    /// # Arguments
    ///
    /// * `row` - The index of the row.
    ///
    /// # Returns
    ///
    /// A reference to the row, or `None` if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::Grid;
    /// use aoc_utils_rust::grid::sized_grid::SizedGrid;
    ///
    /// let grid = SizedGrid::<i32, 2, 3>::from([[1, 2, 3], [4, 5, 6]]);
    /// assert_eq!(grid.get_row(1), Some(&[4, 5, 6][..]));
    /// assert_eq!(grid.get_row(2), None);
    /// ```
    fn get_row(&self, row: usize) -> Option<&[T]> {
        self.matrix.get(row).map(|x| x.as_slice())
    }

    /// Returns a reference to the element at the specified position.
    ///
    /// # Arguments
    ///
    /// * `position` - The position of the element.
    ///
    /// # Returns
    ///
    /// An `Option` containing a reference to the element, or `None` if the position is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::sized_grid::SizedGrid;
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::Grid;
    ///
    /// let grid = SizedGrid::<i32, 2, 3>::from([[1, 2, 3], [4, 5, 6]]);
    /// assert_eq!(grid.get(&Coordinate::new(0, 1)), Some(&2));
    /// assert_eq!(grid.get(&Coordinate::new(2, 3)), None);
    /// ```
    #[inline]
    fn get(&self, position: &Coordinate) -> Option<&T> {
        self.get(position)
    }

    fn is_valid_coordinate(&self, coordinate: &Coordinate) -> bool {
        self.is_valid_coordinate(coordinate)
    }

    /// Creates an iterator over the grid.
    ///
    /// # Returns
    ///
    /// A `GridIter` over the grid.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::Grid;
    /// use self::aoc_utils_rust::grid::sized_grid::SizedGrid;
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    ///
    /// let grid = SizedGrid::<i32, 2, 3>::from([[1, 2, 3], [4, 5, 6]]);
    /// let mut iter = grid.iter();
    /// let mut first_row = iter.next().unwrap();
    /// let first_element = first_row.next().unwrap();
    /// assert_eq!(first_element, (Coordinate::new(0, 0), &1));
    /// ```
    fn iter<'a>(&'a self) -> GridIter<'a, Self, T>
    where
        T: 'a,
    {
        GridIter::new(self)
    }
}

impl<T, const N: usize, const M: usize> GridMut<T> for SizedGrid<T, N, M> {
    /// Returns a mutable reference to the row at the specified index.
    ///
    /// # Arguments
    ///
    /// * `row` - The index of the row.
    ///
    /// # Returns
    ///
    /// An `Option` containing a mutable reference to the row, or `None` if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::sized_grid::SizedGrid;
    /// use aoc_utils_rust::grid::{Grid, GridMut};
    ///
    /// let mut grid = SizedGrid::<i32, 2, 3>::from([[1, 2, 3], [4, 5, 6]]);
    /// let row = grid.get_row_mut(1).unwrap();
    /// row[2] = 10;
    /// assert_eq!(grid.get(&Coordinate::new(1, 2)), Some(&10));
    /// ```
    fn get_row_mut(&mut self, row: usize) -> Option<&mut [T]> {
        self.matrix.get_mut(row).map(|x| x.as_mut())
    }

    /// Returns a mutable reference to the element at the specified position.
    ///
    /// # Arguments
    ///
    /// * `position` - The position of the element.
    ///
    /// # Returns
    ///
    /// An `Option` containing a mutable reference to the element, or `None` if the position is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::sized_grid::SizedGrid;
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::{Grid, GridMut};
    ///
    /// let mut grid = SizedGrid::<i32, 2, 3>::from([[1, 2, 3], [4, 5, 6]]);
    /// let coordinate = Coordinate::new(1, 2);
    /// if let Some(value) = grid.get_mut(&coordinate) {
    ///     *value = 10;
    /// }
    /// assert_eq!(grid.get(&coordinate), Some(&10));
    /// ```
    #[inline(always)]
    fn get_mut(&mut self, position: &Coordinate) -> Option<&mut T> {
        if self.is_valid_coordinate(&position) {
            Some(&mut self.matrix[position.i as usize][position.j as usize])
        } else {
            None
        }
    }
}
pub mod iterator {
    use crate::grid::iterators::RowIterMut;
    use crate::grid::sized_grid::SizedGrid;
    use std::iter::Enumerate;
    use std::marker::PhantomData;
    use std::slice::IterMut;

    /// An iterator over the rows of a mutable `SizedGrid`.
    ///
    /// # Type Parameters
    ///
    /// * `'a` - The lifetime of the references to the grid and its elements.
    /// * `T` - The type of elements stored in the grid.
    /// * `ROW` - The number of rows in the grid.
    /// * `COL` - The number of columns in the grid.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::sized_grid::SizedGrid;
    /// use aoc_utils_rust::grid::GridMut;
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    ///
    /// let mut grid = SizedGrid::<i32, 2, 3>::from([[1, 2, 3], [4, 5, 6]]);
    /// let mut iter = grid.iter_mut();
    ///
    /// let mut row_iter = iter.next().unwrap();
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 0), &mut 1)));
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 1), &mut 2)));
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 2), &mut 3)));
    /// assert_eq!(row_iter.next(), None);
    ///
    /// let mut row_iter = iter.next().unwrap();
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(1, 0), &mut 4)));
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(1, 1), &mut 5)));
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(1, 2), &mut 6)));
    /// assert_eq!(row_iter.next(), None);
    ///
    /// assert_eq!(iter.next(), None);
    /// ```
    pub struct GridIterMut<'a, T, const ROW: usize, const COL: usize>
    where
        T: 'a,
    {
        grid_rows: Enumerate<IterMut<'a, [T; COL]>>,
        _marker: PhantomData<&'a mut T>,
    }

    impl<'a, T, const ROW: usize, const COL: usize> GridIterMut<'a, T, ROW, COL>
    where
        T: 'a,
    {
        /// Creates a new `GridIterMut` for the given `SizedGrid`.
        ///
        /// # Arguments
        ///
        /// * `grid` - A mutable reference to the `SizedGrid`.
        ///
        /// # Returns
        ///
        /// A new `GridIterMut` instance.
        pub(super) fn new(grid: &'a mut SizedGrid<T, ROW, COL>) -> Self {
            let enumerated_rows = grid.matrix.iter_mut().enumerate();
            Self {
                grid_rows: enumerated_rows,
                _marker: PhantomData,
            }
        }
    }

    impl<'a, T, const ROW: usize, const COL: usize> Iterator for GridIterMut<'a, T, ROW, COL>
    where
        T: 'a,
    {
        type Item = RowIterMut<'a, T>;

        /// Advances the iterator and returns the next row iterator.
        ///
        /// # Returns
        ///
        /// An `Option` containing the next `RowIterMut`, or `None` if there are no more rows.
        ///
        /// # Examples
        ///
        /// ```
        /// use aoc_utils_rust::grid::sized_grid::SizedGrid;
        /// use aoc_utils_rust::grid::GridMut;
        /// use aoc_utils_rust::coordinate_system::Coordinate;
        ///
        /// let mut grid = SizedGrid::<i32, 2, 3>::from([[1, 2, 3], [4, 5, 6]]);
        /// let mut iter = grid.iter_mut();
        ///
        /// let mut row_iter = iter.next().unwrap();
        /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 0), &mut 1)));
        /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 1), &mut 2)));
        /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 2), &mut 3)));
        /// assert_eq!(row_iter.next(), None);
        ///
        /// let mut row_iter = iter.next().unwrap();
        /// assert_eq!(row_iter.next(), Some((Coordinate::new(1, 0), &mut 4)));
        /// assert_eq!(row_iter.next(), Some((Coordinate::new(1, 1), &mut 5)));
        /// assert_eq!(row_iter.next(), Some((Coordinate::new(1, 2), &mut 6)));
        /// assert_eq!(row_iter.next(), None);
        ///
        /// assert_eq!(iter.next(), None);
        /// ```
        fn next(&mut self) -> Option<Self::Item> {
            if let Some((row, row_item)) = self.grid_rows.next() {
                let row_iter = RowIterMut::new(row_item.as_mut_slice(), row);
                Some(row_iter)
            } else {
                None
            }
        }
    }
}
