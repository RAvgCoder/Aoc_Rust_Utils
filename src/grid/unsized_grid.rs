use crate::coordinate_system::Coordinate;
use crate::grid::iterators::{GridIter, RowIterMut};
use crate::grid::{Grid, GridMut};
use std::fmt::Debug;
use std::iter::Enumerate;
use std::marker::PhantomData;
use std::slice::IterMut;

/// A dynamically sized grid structure.
///
/// # Type Parameters
///
/// * `T` - The type of elements stored in the grid.
///
/// # Examples
///
/// ```
/// use aoc_utils_rust::coordinate_system::Coordinate;
/// use aoc_utils_rust::grid::{Grid, GridMut};
/// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
///
/// // Create a new grid with specified rows and columns, initializing all elements to 0
/// let grid = UnsizedGrid::new(2, 3, 0);
///
/// // Create a new grid from a 2D vector
/// let grid = UnsizedGrid::from(vec![vec![1, 2, 3], vec![4, 5, 6]]);
///
/// // Get the number of rows and columns
/// assert_eq!(grid.num_rows(), 2);
/// assert_eq!(grid.num_cols(), 3);
///
/// // Get an element from the grid
/// let coordinate = Coordinate::new(0, 1);
/// assert_eq!(grid.get(&coordinate), Some(&2));
///
/// // Get a mutable reference to an element in the grid
/// let mut grid = UnsizedGrid::from(vec![vec![1, 2, 3], vec![4, 5, 6]]);
/// let coordinate = Coordinate::new(1, 2);
/// if let Some(value) = grid.get_mut(&coordinate) {
///     *value = 10;
/// }
/// assert_eq!(grid.get(&coordinate), Some(&10));
/// ```
#[repr(transparent)]
pub struct UnsizedGrid<T> {
    matrix: Box<[Box<[T]>]>,
}

impl<T> UnsizedGrid<T> {
    /// Creates a new `UnsizedGrid` with the specified number of rows and columns,
    /// initializing all elements to the provided default value.
    ///
    /// # Arguments
    ///
    /// * `rows` - The number of rows in the grid.
    /// * `cols` - The number of columns in the grid.
    /// * `default` - The default value to initialize each element in the grid.
    ///
    /// # Type Parameters
    ///
    /// * `T` - The type of elements stored in the grid. Must implement the `Clone` trait.
    ///
    /// # Returns
    ///
    /// A new `UnsizedGrid` instance with the specified dimensions and default values.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::Grid;
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    ///
    /// let grid = UnsizedGrid::new(2, 3, 0);
    ///
    /// assert_eq!(grid.num_rows(), 2);
    /// assert_eq!(grid.num_cols(), 3);
    /// assert_eq!(grid.get(&Coordinate::new(0, 1)), Some(&0));
    /// ```
    #[inline]
    pub fn new(rows: usize, cols: usize, default: T) -> Self
    where
        T: Clone,
    {
        // Create a single row filled with the default value, to avoid multiple clones
        // Clone the row for each additional row needed
        Self::from(vec![vec![default; cols]; rows])
    }

    /// Creates an iterator over the grid which allows mutation of `T`.
    ///
    /// # Returns
    ///
    /// A `GridIterMut` over the grid.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    /// use aoc_utils_rust::grid::GridMut;
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    ///
    /// let mut grid = UnsizedGrid::from(vec![vec![1, 2, 3], vec![4, 5, 6]]);
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
    pub fn iter_mut(&mut self) -> GridIterMut<'_, T> {
        GridIterMut::new(self)
    }
}

impl<T: Debug> Debug for UnsizedGrid<T> {
    /// Formats the grid using the given formatter.
    ///
    /// # Arguments
    ///
    /// * `f` - The formatter.
    ///
    /// # Returns
    ///
    /// A `Result` indicating success or failure.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "UnsizedGrid: {{")?;
        for row in self.matrix.iter() {
            for cell in row.iter() {
                write!(f, "{:?}    ", cell)?;
            }
            writeln!(f)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl<T> Grid<T> for UnsizedGrid<T> {
    /// Returns the number of rows in the grid.
    ///
    /// # Returns
    ///
    /// The number of rows in the grid.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    /// use aoc_utils_rust::grid::Grid;
    ///
    /// let grid = UnsizedGrid::from(vec![vec![1, 2, 3], vec![4, 5, 6]]);
    /// assert_eq!(grid.num_rows(), 2);
    /// ```
    #[inline(always)]
    fn num_rows(&self) -> usize {
        self.matrix.len()
    }

    /// Returns the number of columns in the grid.
    ///
    /// # Returns
    ///
    /// The number of columns in the grid.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    /// use aoc_utils_rust::grid::Grid;
    ///
    /// let grid = UnsizedGrid::from(vec![vec![1, 2, 3], vec![4, 5, 6]]);
    /// assert_eq!(grid.num_cols(), 3);
    /// ```
    #[inline(always)]
    fn num_cols(&self) -> usize {
        self.matrix[0].len()
    }

    /// Returns a reference to the row at the specified index.
    ///
    /// # Arguments
    ///
    /// * `row` - The index of the row.
    ///
    /// # Returns
    ///
    /// An `Option` containing a reference to the row, or `None` if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    /// use aoc_utils_rust::grid::Grid;
    ///
    /// let grid = UnsizedGrid::from(vec![vec![1, 2, 3], vec![4, 5, 6]]);
    /// let row = grid.get_row(1).unwrap();
    /// assert_eq!(row, &[4, 5, 6]);
    ///
    /// let invalid_row = grid.get_row(2);
    /// assert!(invalid_row.is_none());
    /// ```
    #[inline(always)]
    fn get_row(&self, row: usize) -> Option<&[T]> {
        self.matrix.get(row).map(|row| row.iter().as_slice())
    }

    /// Returns a reference to the element at the specified coordinate.
    ///
    /// # Arguments
    ///
    /// * `coordinate` - The coordinate of the element.
    ///
    /// # Returns
    ///
    /// An `Option` containing a reference to the element, or `None` if the coordinate is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    /// use aoc_utils_rust::grid::Grid;
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    ///
    /// let grid = UnsizedGrid::from(vec![vec![1, 2, 3], vec![4, 5, 6]]);
    /// let coordinate = Coordinate::new(1, 2);
    /// assert_eq!(grid.get(&coordinate), Some(&6));
    ///
    /// let invalid_coordinate = Coordinate::new(2, 3);
    /// assert_eq!(grid.get(&invalid_coordinate), None);
    /// ```
    #[inline(always)]
    fn get(&self, coordinate: &Coordinate) -> Option<&T> {
        if self.is_valid_coordinate(coordinate) {
            Some(&self.matrix[coordinate.i as usize][coordinate.j as usize])
        } else {
            None
        }
    }

    /// Returns an iterator over the elements of the grid.
    ///
    /// # Type Parameters
    /// * `'a` - The lifetime of the references to the grid and its elements.
    ///
    /// # Returns
    /// A `GridIter` that iterates over the elements of the grid.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    /// use aoc_utils_rust::grid::iterators::GridIter;
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::Grid;
    ///
    /// let grid = UnsizedGrid::from(vec![vec![1, 2, 3], vec![4, 5, 6]]);
    /// let mut iter = grid.iter();
    ///
    /// let mut row_iter = iter.next().unwrap();
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 0), &1)));
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 1), &2)));
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 2), &3)));
    /// assert_eq!(row_iter.next(), None);
    ///
    /// let mut row_iter = iter.next().unwrap();
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(1, 0), &4)));
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(1, 1), &5)));
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(1, 2), &6)));
    /// assert_eq!(row_iter.next(), None);
    ///
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline(always)]
    fn iter<'a>(&'a self) -> GridIter<'a, Self, T>
    where
        T: 'a,
    {
        GridIter::new(self, 0)
    }
}

impl<T> GridMut<T> for UnsizedGrid<T> {
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
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    /// use aoc_utils_rust::grid::{Grid, GridMut};
    ///
    /// let mut grid = UnsizedGrid::from(vec![vec![1, 2, 3], vec![4, 5, 6]]);
    /// let row = grid.get_row_mut(1).unwrap();
    /// row[2] = 10;
    /// assert_eq!(grid.get(&Coordinate::new(1, 2)), Some(&10));
    /// ```
    fn get_row_mut(&mut self, row: usize) -> Option<&mut [T]> {
        self.matrix.get_mut(row).map(|x| x.as_mut())
    }

    /// Returns a mutable reference to the element at the specified coordinate.
    ///
    /// # Arguments
    ///
    /// * `coordinate` - The coordinate of the element.
    ///
    /// # Returns
    ///
    /// An `Option` containing a mutable reference to the element, or `None` if the coordinate is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    /// use aoc_utils_rust::grid::{Grid, GridMut};
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    ///
    /// let mut grid = UnsizedGrid::from(vec![vec![1, 2, 3], vec![4, 5, 6]]);
    /// let coordinate = Coordinate::new(1, 2);
    /// if let Some(value) = grid.get_mut(&coordinate) {
    ///     *value = 10;
    /// }
    /// assert_eq!(grid.get(&coordinate), Some(&10));
    /// ```
    fn get_mut(&mut self, coordinate: &Coordinate) -> Option<&mut T> {
        if self.is_valid_coordinate(coordinate) {
            Some(&mut self.matrix[coordinate.i as usize][coordinate.j as usize])
        } else {
            None
        }
    }
}

impl<T> From<Vec<Vec<T>>> for UnsizedGrid<T> {
    /// Creates a new `UnsizedGrid` from a 2D vector.
    ///
    /// # Arguments
    ///
    /// * `grid` - A 2D vector representing the grid.
    ///
    /// # Returns
    ///
    /// A new `UnsizedGrid` instance.
    ///
    /// # Panics
    ///
    /// Panics if the provided grid is empty or if any row in the grid is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::Grid;
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    ///
    /// let grid = vec![vec![1, 2, 3], vec![4, 5, 6]];
    /// let unsized_grid = UnsizedGrid::from(grid);
    ///
    /// assert_eq!(unsized_grid.num_rows(), 2);
    /// assert_eq!(unsized_grid.num_cols(), 3);
    /// assert_eq!(unsized_grid.get(&Coordinate::new(0, 1)), Some(&2));
    /// ```
    #[inline(always)]
    fn from(grid: Vec<Vec<T>>) -> Self {
        Self::from(
            grid.into_iter()
                .map(|row| row.into_boxed_slice())
                .collect::<Vec<Box<[T]>>>()
                .into_boxed_slice(),
        )
    }
}

impl<T> From<Box<[Box<[T]>]>> for UnsizedGrid<T> {
    /// Creates a new `UnsizedGrid` from a boxed 2D slice.
    ///
    /// # Arguments
    ///
    /// * `grid` - A boxed 2D slice representing the grid.
    ///
    /// # Returns
    ///
    /// A new `UnsizedGrid` instance.
    ///
    /// # Panics
    ///
    /// Panics if the provided grid is empty or if any row in the grid is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::Grid;
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    ///
    /// let grid = vec![vec![1, 2, 3].into_boxed_slice(), vec![4, 5, 6].into_boxed_slice()].into_boxed_slice();
    /// let unsized_grid = UnsizedGrid::from(grid);
    ///
    /// assert_eq!(unsized_grid.num_rows(), 2);
    /// assert_eq!(unsized_grid.num_cols(), 3);
    /// assert_eq!(unsized_grid.get(&Coordinate::new(0, 1)), Some(&2));
    /// ```
    #[inline(always)]
    fn from(grid: Box<[Box<[T]>]>) -> Self {
        assert!(!grid.is_empty(), "Grid cannot be empty");
        assert!(!grid[0].is_empty(), "Grid rows cannot be empty");
        Self { matrix: grid }
    }
}

/// An iterator over the rows of a mutable `UnsizedGrid`.
///
/// # Type Parameters
///
/// * `'a` - The lifetime of the references to the grid and its elements.
/// * `T` - The type of elements stored in the grid.
///
/// # Examples
///
/// ```
/// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
/// use aoc_utils_rust::grid::GridMut;
/// use aoc_utils_rust::coordinate_system::Coordinate;
///
/// let mut grid = UnsizedGrid::from(vec![vec![1, 2, 3], vec![4, 5, 6]]);
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
pub struct GridIterMut<'a, T>
where
    T: 'a,
{
    grid_rows: Enumerate<IterMut<'a, Box<[T]>>>,
    _marker: PhantomData<&'a mut T>,
}

impl<'a, T> GridIterMut<'a, T>
where
    T: 'a,
{
    pub(self) fn new(grid: &'a mut UnsizedGrid<T>) -> Self {
        let enumerated_rows: Enumerate<IterMut<Box<[T]>>> = grid.matrix.iter_mut().enumerate();
        Self {
            grid_rows: enumerated_rows,
            _marker: PhantomData,
        }
    }
}

impl<'a, T> Iterator for GridIterMut<'a, T>
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
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    /// use aoc_utils_rust::grid::GridMut;
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    ///
    /// let mut grid = UnsizedGrid::from(vec![vec![1, 2, 3], vec![4, 5, 6]]);
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
            let row_iter = RowIterMut::new(row_item.as_mut(), row);
            Some(row_iter)
        } else {
            None
        }
    }
}

