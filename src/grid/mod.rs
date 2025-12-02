use crate::coordinate_system::Coordinate;
pub use crate::grid::iterators::GridIter;
use crate::grid::iterators::{GridIterMut, RowIterMut};

pub mod grid_slice;
pub mod sized_grid;
pub mod unsized_grid;

/// The `Grid` trait defines the interface for a grid structure.
/// It provides methods to get the number of rows and columns,
/// access rows and individual elements, and check if a coordinate is valid.
///
/// # Examples
///
/// ```
/// use self::aoc_utils_rust::grid::Grid;
/// use self::aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
/// use self::aoc_utils_rust::coordinate_system::Coordinate;
///
/// let grid = UnsizedGrid::from(vec![vec![1, 2, 3], vec![4, 5, 6]]);
/// assert_eq!(grid.num_rows(), 2);
/// assert_eq!(grid.num_cols(), 3);
/// assert_eq!(grid.get(&Coordinate::new(0, 1)), Some(&2));
/// assert!(grid.is_valid_coordinate(&Coordinate::new(1, 2)));
/// assert!(!grid.is_valid_coordinate(&Coordinate::new(2, 3)));
/// ```
pub trait Grid<T> {
    /// Returns the number of rows in the grid.
    fn num_rows(&self) -> usize;

    /// Returns the number of columns in the grid.
    fn num_cols(&self) -> usize;

    /// Returns a reference to the row at the specified index.
    ///
    /// # Arguments
    ///
    /// * `row` - The index of the row.
    ///
    /// # Returns
    ///
    /// A reference to the row.
    fn get_row(&self, row: usize) -> Option<&[T]>;

    /// Returns a reference to the element at the specified coordinate, if valid.
    ///
    /// # Arguments
    ///
    /// * `coordinate` - The coordinate of the element.
    ///
    /// # Returns
    ///
    /// An `Option` containing a reference to the element, or `None` if the coordinate is invalid.
    fn get(&self, coordinate: &Coordinate) -> Option<&T>;

    /// Checks if the specified coordinate is valid within the grid.
    ///
    /// # Arguments
    ///
    /// * `coordinate` - The coordinate to check.
    ///
    /// # Returns
    ///
    /// `true` if the coordinate is valid, `false` otherwise.
    fn is_valid_coordinate(&self, coordinate: &Coordinate) -> bool {
        (0..self.num_rows()).contains(&(coordinate.i as usize))
            && (0..self.num_cols()).contains(&(coordinate.j as usize))
    }

    /// Returns the coordinate of the bottom right element in the grid.
    ///
    /// # Returns
    /// A `Coordinate` representing the position of the bottom right element in the grid.
    fn bottom_right_coordinate(&self) -> Coordinate {
        Coordinate::new((self.num_rows() - 1) as i32, (self.num_cols() - 1) as i32)
    }

    /// Returns an iterator over the elements of the grid.
    ///
    /// # Type Parameters
    /// * `'a` - The lifetime of the references to the grid and its elements.
    ///
    /// # Returns
    /// A `GridIter` that iterates over the elements of the grid.
    fn iter<'a>(&'a self) -> GridIter<'a, Self, T>
    where
        T: 'a,
        Self: Sized;
}

/// The `GridMut` trait extends the `Grid` trait to provide mutable access to the grid elements.
///
/// # Examples
///
/// ```
/// use self::aoc_utils_rust::grid::{Grid, GridMut};
/// use self::aoc_utils_rust::grid::sized_grid::SizedGrid;
/// use self::aoc_utils_rust::coordinate_system::Coordinate;
///
/// let mut grid = SizedGrid::<i32, 2, 3>::from([[1, 2, 3], [4, 5, 6]]);
/// assert_eq!(grid.num_rows(), 2);
/// assert_eq!(grid.num_cols(), 3);
/// assert_eq!(grid.get(&Coordinate::new(0, 1)), Some(&2));
/// assert!(grid.is_valid_coordinate(&Coordinate::new(1, 2)));
/// assert!(!grid.is_valid_coordinate(&Coordinate::new(2, 3)));
/// set_value(&mut grid, Coordinate::new(0, 1), 10);
///
/// fn set_value<G>(grid: &mut G, coordinate: Coordinate, value: i32)
/// where
///  G: GridMut<i32> {
///     if let Some(value) = grid.get_mut(&Coordinate::new(0, 1)) {
///         *value = 10;
///     }
/// }
///
/// assert_eq!(grid.get(&Coordinate::new(0, 1)), Some(&10));
///
/// let row = grid.get_row_mut(1).unwrap();
/// row[0] = 20;
/// assert_eq!(grid.get(&Coordinate::new(1, 0)), Some(&20));
/// ```
pub trait GridMut<T>: Grid<T> {
    /// Returns a mutable reference to the row at the specified index.
    ///
    /// # Arguments
    ///
    /// * `row` - The index of the row.
    ///
    /// # Returns
    ///
    /// A mutable reference to the row.
    fn get_row_mut(&mut self, row: usize) -> Option<&mut [T]>;

    /// Returns a mutable reference to the element at the specified coordinate, if valid.
    ///
    /// # Arguments
    ///
    /// * `coordinate` - The coordinate of the element.
    ///
    /// # Returns
    ///
    /// An `Option` containing a mutable reference to the element, or `None` if the coordinate is invalid.
    fn get_mut(&mut self, coordinate: &Coordinate) -> Option<&mut T>;

    /// Returns an iterator over the rows of the grid, allowing mutable access to each row.
    ///
    /// # Type Parameters
    ///
    /// * `'a` - The lifetime of the references to the grid and its elements.
    /// * `I` - The type of the iterator over mutable row iterators.
    ///
    /// # Returns
    ///
    /// A `GridIterMut` that iterates over the rows of the grid, allowing mutable access to each row.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::GridMut;
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    /// use aoc_utils_rust::grid::iterators::{GridIterMut, RowIterMut};
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
    fn iter_mut(&mut self) -> GridIterMut<T, impl Iterator<Item = RowIterMut<T>>>;
}

pub mod iterators {
    use crate::coordinate_system::Coordinate;
    use crate::grid::Grid;
    use std::marker::PhantomData;

    /// An iterator over the rows of a grid.
    ///
    /// # Type Parameters
    ///
    /// * `'a` - The lifetime of the references to the grid and its elements.
    /// * `G` - The type of the grid.
    /// * `T` - The type of the elements in the grid.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::iterators::RowIter;
    /// use self::aoc_utils_rust::grid::{Grid, GridIter};
    /// use self::aoc_utils_rust::grid::sized_grid::SizedGrid;
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    ///
    /// let grid = SizedGrid::<i32, 2, 3>::from([[1, 2, 3], [4, 5, 6]]);
    /// let mut iter: GridIter<SizedGrid<i32, 2, 3>, i32> = grid.iter();
    /// let mut first_row: RowIter<i32> = iter.next().unwrap();
    /// let first_element = first_row.next().unwrap();
    /// assert_eq!(first_element, (Coordinate::new(0, 0), &1));
    /// ```
    #[derive(Debug, Clone, Eq, PartialEq)]
    pub struct GridIter<'a, G, T>
    where
        G: Grid<T>,
        T: 'a,
    {
        grid: &'a G,
        row: usize,
        _marker: PhantomData<&'a T>,
    }

    impl<'a, G, T> GridIter<'a, G, T>
    where
        G: Grid<T>,
    {
        /// Creates a new `GridIter` for the given grid.
        ///
        /// # Arguments
        ///
        /// * `grid` - A reference to the grid to iterate over.
        ///
        /// # Returns
        ///
        /// A new `GridIter` instance.
        ///
        /// # Examples
        ///
        /// ```
        /// use aoc_utils_rust::grid::{Grid, GridIter};
        /// use aoc_utils_rust::grid::sized_grid::SizedGrid;
        /// use aoc_utils_rust::coordinate_system::Coordinate;
        ///
        /// let grid = SizedGrid::<i32, 2, 3>::from([[1, 2, 3], [4, 5, 6]]);
        /// let mut iter = grid.iter();
        /// let mut first_row = iter.next().unwrap();
        /// let first_element = first_row.next().unwrap();
        /// assert_eq!(first_element, (Coordinate::new(0, 0), &1));
        /// ```
        #[inline(always)]
        pub(crate) const fn new(grid: &'a G) -> Self {
            Self {
                grid,
                row: 0,
                _marker: PhantomData,
            }
        }
    }

    impl<'a, G, T> Iterator for GridIter<'a, G, T>
    where
        G: Grid<T>,
    {
        type Item = RowIter<'a, T>;

        /// Advances the iterator and returns the next row iterator.
        ///
        /// # Returns
        ///
        /// An `Option` containing the next `RowIter`, or `None` if there are no more rows.
        ///
        /// # Examples
        ///
        /// ```
        /// use aoc_utils_rust::grid::{Grid, GridIter};
        /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
        /// use aoc_utils_rust::coordinate_system::Coordinate;
        ///
        /// let grid = UnsizedGrid::from(vec![vec![1, 2, 3], vec![4, 5, 6]]);
        /// let mut iter = grid.iter();
        /// let mut first_row = iter.next().unwrap();
        /// let first_element = first_row.next().unwrap();
        /// assert_eq!(first_element, (Coordinate::new(0, 0), &1));
        /// ```
        #[inline(always)]
        fn next(&mut self) -> Option<Self::Item> {
            self.grid.get_row(self.row).map(|row| {
                let row_iter = RowIter::new(row, self.row);
                self.row += 1;
                row_iter
            })
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            let remaining_rows = self.grid.num_rows() - self.row;
            (remaining_rows, Some(remaining_rows))
        }
    }

    /// An iterator over the elements of a row in a grid.
    ///
    /// # Type Parameters
    /// * `'a` - The lifetime of the references to the row elements.
    /// * `T` - The type of the elements in the row.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::Grid;
    ///
    /// let grid = UnsizedGrid::from(vec![vec![1, 2, 3], vec![4, 5, 6]]);
    /// let mut row_iter = grid.iter().next().unwrap();
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 0), &1)));
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 1), &2)));
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 2), &3)));
    /// assert_eq!(row_iter.next(), None);
    /// ```
    #[derive(Debug, Clone, Eq, PartialEq)]
    pub struct RowIter<'a, T> {
        /// A reference to the slice of row elements.
        row_item: &'a [T],
        /// The index of the current row.
        row: usize,
        /// The index of the current column.
        col: usize,
        /// A marker to indicate the lifetime of the row elements.
        _marker: PhantomData<&'a T>,
    }

    impl<'a, T> RowIter<'a, T> {
        /// Creates a new `RowIter` for the given row.
        ///
        /// # Arguments
        ///
        /// * `row_item` - A reference to the slice of row elements.
        /// * `row` - The index of the current row.
        /// * `col` - The index of the current column.
        ///
        /// # Returns
        ///
        /// A new `RowIter` instance.
        ///
        /// # Examples
        ///
        /// ```
        /// use aoc_utils_rust::coordinate_system::Coordinate;
        /// use aoc_utils_rust::grid::Grid;
        /// use aoc_utils_rust::grid::iterators::RowIter;
        /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
        ///
        ///
        /// let grid = UnsizedGrid::from(vec![vec![1, 2, 3], vec![4, 5, 6]]);
        /// let mut row_iter = grid.iter().next().unwrap();
        /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 0), &1)));
        /// ```
        #[inline(always)]
        pub(crate) const fn new(row_item: &'a [T], row: usize) -> Self {
            Self {
                row_item,
                row,
                col: 0,
                _marker: PhantomData,
            }
        }
    }

    impl<'a, T> Iterator for RowIter<'a, T> {
        type Item = (Coordinate, &'a T);

        /// Advances the iterator and returns the next element in the row.
        ///
        /// # Returns
        ///
        /// An `Option` containing a tuple with the `Coordinate` and a reference to the element, or `None` if there are no more elements.
        ///
        /// # Examples
        ///
        /// ```
        /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
        /// use aoc_utils_rust::coordinate_system::Coordinate;
        /// use aoc_utils_rust::grid::Grid;
        ///
        /// let grid = UnsizedGrid::from(vec![vec![1, 2, 3], vec![4, 5, 6]]);
        /// let mut row_iter = grid.iter().next().unwrap();
        /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 0), &1)));
        /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 1), &2)));
        /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 2), &3)));
        /// assert_eq!(row_iter.next(), None);
        /// ```
        fn next(&mut self) -> Option<Self::Item> {
            let items = std::mem::take(&mut self.row_item);
            if let Some((item, rest)) = items.split_first() {
                self.row_item = rest;
                let coordinate = Coordinate::new(self.row as i32, self.col as i32);
                self.col += 1;
                Some((coordinate, item))
            } else {
                None
            }
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            let remaining_cols = self.row_item.len();
            (remaining_cols, Some(remaining_cols))
        }
    }

    /// An iterator over the rows of a mutable `UnsizedGrid`.
    ///
    /// # Type Parameters
    ///
    /// * `'a` - The lifetime of the references to the grid and its elements.
    /// * `T` - The type of elements stored in the grid.
    /// * `I` - The type of the iterator over mutable row iterators.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::GridMut;
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    /// use aoc_utils_rust::grid::iterators::{GridIterMut, RowIterMut};
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
    pub struct GridIterMut<'a, T, I>
    where
        I: Iterator<Item = RowIterMut<'a, T>>,
        T: 'a,
    {
        grid_rows: I,
    }

    impl<'a, T, I> GridIterMut<'a, T, I>
    where
        I: Iterator<Item = RowIterMut<'a, T>>,
    {
        pub(crate) fn new(iter: I) -> Self {
            Self { grid_rows: iter }
        }
    }

    impl<'a, T, I> Iterator for GridIterMut<'a, T, I>
    where
        I: Iterator<Item = RowIterMut<'a, T>>,
    {
        type Item = RowIterMut<'a, T>;

        /// Advances the iterator and returns the next mutable row iterator.
        ///
        /// # Returns
        ///
        /// An `Option` containing the next `RowIterMut`, or `None` if there are no more rows.
        ///
        /// # Examples
        ///
        /// ```
        /// use aoc_utils_rust::coordinate_system::Coordinate;
        /// use aoc_utils_rust::grid::GridMut;
        /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
        /// use aoc_utils_rust::grid::iterators::{GridIterMut, RowIterMut};
        ///
        /// let mut grid = UnsizedGrid::from(vec![vec![1, 2, 3], vec![4, 5, 6]]);
        /// let mut iter = grid.iter_mut();
        ///
        /// let mut row_iter = iter.next().unwrap();
        /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 0), &mut 1)));
        /// ```
        fn next(&mut self) -> Option<Self::Item> {
            self.grid_rows.next()
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            self.grid_rows.size_hint()
        }
    }

    /// An iterator over the elements of a row in a grid.
    ///
    /// # Type Parameters
    /// * `'a` - The lifetime of the references to the row elements.
    /// * `T` - The type of the elements in the row.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::GridMut;
    ///
    /// let mut grid = UnsizedGrid::from(vec![vec![1, 2, 3], vec![4, 5, 6]]);
    /// let mut row_iter = grid.iter_mut().next().unwrap();
    ///
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 0), &mut 1)));
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 1), &mut 2)));
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 2), &mut 3)));
    /// assert_eq!(row_iter.next(), None);
    /// ```
    #[derive(Debug, Eq, PartialEq)]
    pub struct RowIterMut<'a, T> {
        row_item: &'a mut [T],
        row: usize,
        col: usize,
    }

    impl<'a, T> RowIterMut<'a, T> {
        #[inline(always)]
        pub(crate) fn new(row_item: &'a mut [T], row: usize) -> Self {
            Self {
                row_item,
                row,
                col: 0,
            }
        }
    }

    impl<'a, T> Iterator for RowIterMut<'a, T> {
        type Item = (Coordinate, &'a mut T);

        /// Advances the iterator and returns the next element in the row.
        ///
        /// # Returns
        ///
        /// An `Option` containing a tuple with the `Coordinate` and a mutable reference to the element, or `None` if there are no more elements.
        ///
        /// # Examples
        ///
        /// ```
        /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
        /// use aoc_utils_rust::coordinate_system::Coordinate;
        /// use aoc_utils_rust::grid::GridMut;
        ///
        /// let mut grid = UnsizedGrid::from(vec![vec![1, 2, 3], vec![4, 5, 6]]);
        /// let mut row_iter = grid.iter_mut().next().unwrap();
        ///
        /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 0), &mut 1)));
        /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 1), &mut 2)));
        /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 2), &mut 3)));
        /// assert_eq!(row_iter.next(), None);
        /// ```
        fn next(&mut self) -> Option<Self::Item> {
            let items = std::mem::take(&mut self.row_item);
            if let Some((item, rest)) = items.split_first_mut() {
                self.row_item = rest;
                let coordinate = Coordinate::new(self.row as i32, self.col as i32);
                self.col += 1;
                Some((coordinate, item))
            } else {
                None
            }
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            let remaining_cols = self.row_item.len() - self.col;
            (remaining_cols, Some(remaining_cols))
        }
    }
}
