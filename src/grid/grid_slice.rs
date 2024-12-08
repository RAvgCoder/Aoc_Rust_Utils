use crate::coordinate_system::Coordinate;
use crate::grid::{Grid, GridIter};
use std::marker::PhantomData;
use std::ops::RangeInclusive;

/// A view into a subset of a grid, defined by row and column ranges.
///
/// # Type Parameters
/// * `'grid` - The lifetime of the grid reference.
/// * `G` - The type of the grid, which must implement the `Grid` trait.
/// * `T` - The type of the elements in the grid, which must live at least as long as `'grid`.
///
/// # Examples
///
/// ```
/// use aoc_utils_rust::grid::grid_slice::GridSlice;
/// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
/// use aoc_utils_rust::coordinate_system::Coordinate;
/// use aoc_utils_rust::grid::Grid;
///
/// let grid = UnsizedGrid::from_vec(vec![vec![1, 2, 3], vec![4, 5, 6]]);
/// let grid_slice = GridSlice::new(&grid, 0..=1, 0..=0).unwrap();
///
/// assert_eq!(grid_slice.get(&Coordinate::new(0, 0)), Some(&1));
/// assert_eq!(grid_slice.get(&Coordinate::new(1, 2)), None);
/// assert_eq!(grid_slice.get(&Coordinate::new(2, 0)), None);
/// ```
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct GridSlice<'grid, G, T>
where
    G: Grid<T>,
    T: 'grid,
{
    /// A reference to the grid.
    grid: &'grid G,
    /// The range of rows included in the view.
    row: RangeInclusive<usize>,
    /// The range of columns included in the view.
    col: RangeInclusive<usize>,
    /// Marker to indicate that GridView logically contains references to `T` with lifetime `'grid`.
    _marker: PhantomData<&'grid T>,
}

impl<'grid, G, T> GridSlice<'grid, G, T>
where
    G: Grid<T>,
{
    /// Creates a new `GridView` from the given grid and row/column ranges.
    ///
    /// # Arguments
    /// * `grid` - A reference to the grid.
    /// * `row` - The range of rows to include in the view.
    /// * `col` - The range of columns to include in the view.
    ///
    /// # Returns
    /// A Result of new `GridView` instance or `Result::Err` of the range is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::grid_slice::GridSlice;
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::Grid;
    ///
    /// let grid = UnsizedGrid::from_vec(vec![vec![1, 2, 3], vec![4, 5, 6]]);
    /// let grid_slice = GridSlice::new(&grid, 0..=1, 0..=1).unwrap();
    ///
    /// assert_eq!(grid_slice.get(&Coordinate::new(0, 0)), Some(&1));
    /// assert_eq!(grid_slice.get(&Coordinate::new(1, 1)), Some(&5));
    /// assert_eq!(grid_slice.get(&Coordinate::new(2, 0)), None);
    /// ```
    pub fn new(
        grid: &'grid G,
        row: RangeInclusive<usize>,
        col: RangeInclusive<usize>,
    ) -> Result<Self, ()> {
        if grid
            .get(&Coordinate::new(*row.start() as i32, *col.start() as i32))
            .is_some()
        {
            if grid
                .get(&Coordinate::new(*row.end() as i32, *col.end() as i32))
                .is_some()
            {
                return Ok(Self {
                    grid,
                    row,
                    col,
                    _marker: PhantomData,
                });
            }
        }

        Err(())
    }

    /// Creates a new `GridView` from an existing `GridView` and new row/column ranges.
    ///
    /// # Arguments
    /// * `grid` - A reference to an existing `GridView`.
    /// * `row` - The new range of rows to include in the view.
    /// * `col` - The new range of columns to include in the view.
    ///
    /// # Returns
    /// A new `GridView` instance if all ranges are inbounds else an Error .
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::grid_slice::GridSlice;
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::Grid;
    ///
    /// let grid = UnsizedGrid::from_vec(vec![vec![1, 2, 3], vec![4, 5, 6]]);
    /// let grid_slice = GridSlice::new(&grid, 0..=0, 0..=0).unwrap();
    /// let _ = GridSlice::from_slice(&grid_slice, 0..=2, 0..=0).unwrap_err(); // 0..=2 is out of bounds
    /// let new_slice = GridSlice::from_slice(&grid_slice, 0..=0, 0..=0).unwrap();
    ///
    /// assert_eq!(new_slice.get(&Coordinate::new(0, 0)), Some(&1));
    /// assert_eq!(new_slice.get(&Coordinate::new(0, 1)), None);
    /// assert_eq!(new_slice.get(&Coordinate::new(1, 0)), None);
    /// ```
    pub fn from_slice(
        grid: &GridSlice<'grid, G, T>,
        row: RangeInclusive<usize>,
        col: RangeInclusive<usize>,
    ) -> Result<Self, ()> {
        if grid
            .get(&Coordinate::new(*row.start() as i32, *col.start() as i32))
            .is_some()
        {
            if grid
                .get(&Coordinate::new(*row.end() as i32, *col.end() as i32))
                .is_some()
            {
                return Ok(Self {
                    grid: grid.grid,
                    row,
                    col,
                    _marker: PhantomData,
                });
            }
        }

        Err(())
    }
}

impl<'grid, G, T> Grid<T> for GridSlice<'grid, G, T>
where
    G: Grid<T>,
{
    fn num_rows(&self) -> usize {
        *self.row.end()
    }

    fn num_cols(&self) -> usize {
        *self.col.end()
    }

    /// Gets a slice of the specified row within the column range of the view.
    ///
    /// # Arguments
    /// * `row` - The index of the row to retrieve.
    ///
    /// # Returns
    /// A slice of the row within the column range of the view.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::Grid;
    /// use aoc_utils_rust::grid::grid_slice::GridSlice;
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    ///
    /// let grid = UnsizedGrid::from_vec(vec![vec![1, 2, 3], vec![4, 5, 6]]);
    /// let grid_slice = GridSlice::new(&grid, 0..=1, 0..=2).unwrap();
    ///
    /// assert_eq!(grid_slice.get_row(0), Some([1, 2, 3].as_slice()));
    /// assert_eq!(grid_slice.get_row(1), Some([4, 5, 6].as_slice()));
    /// ```
    fn get_row(&self, row: usize) -> Option<&[T]> {
        if self.row.contains(&row) {
            self.grid.get_row(row).map(|row| &row[self.col.clone()])
        } else {
            None
        }
    }

    /// Gets a reference to the element at the specified coordinate, if it is within the view.
    ///
    /// # Arguments
    /// * `coordinate` - The coordinate of the element to retrieve.
    ///
    /// # Returns
    /// An `Option` containing a reference to the element, or `None` if the coordinate is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::grid_slice::GridSlice;
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::Grid;
    ///
    /// let grid = UnsizedGrid::from_vec(vec![vec![1, 2, 3], vec![4, 5, 6]]);
    /// let grid_slice = GridSlice::new(&grid, 0..=1, 0..=0).unwrap();
    ///
    /// assert_eq!(grid_slice.get(&Coordinate::new(0, 0)), Some(&1));
    /// assert_eq!(grid_slice.get(&Coordinate::new(1, 2)), None);
    /// ```
    fn get(&self, coordinate: &Coordinate) -> Option<&T> {
        if !self.is_valid_coordinate(coordinate) {
            return None;
        }
        self.grid.get(coordinate)
    }

    /// Checks if the specified position is within the bounds of the view.
    ///
    /// # Arguments
    /// * `position` - The coordinate to check.
    ///
    /// # Returns
    /// `true` if the position is within the view, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::grid_slice::GridSlice;
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::Grid;
    ///
    /// let grid = UnsizedGrid::from_vec(vec![vec![1, 2, 3], vec![4, 5, 6]]);
    /// let grid_slice = GridSlice::new(&grid, 0..=1, 0..=2).unwrap();
    ///
    /// assert!(grid_slice.is_valid_coordinate(&Coordinate::new(0, 0)));
    /// assert!(grid_slice.is_valid_coordinate(&Coordinate::new(1, 2)));
    /// assert!(!grid_slice.is_valid_coordinate(&Coordinate::new(2, 0)));
    /// assert!(!grid_slice.is_valid_coordinate(&Coordinate::new(0, 3)));
    /// ```
    fn is_valid_coordinate(&self, coordinate: &Coordinate) -> bool {
        self.row.contains(&(coordinate.i as usize)) && self.col.contains(&(coordinate.j as usize))
    }

    /// Returns an iterator over the elements in the view.
    ///
    /// # Returns
    /// An iterator over the elements in the view.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::grid_slice::GridSlice;
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::Grid;
    ///
    /// let grid = UnsizedGrid::from_vec(vec![
    ///         vec![1, 2, 3, 4],
    ///         vec![5, 6, 7, 8],
    ///         vec![9, 10, 11, 12],
    ///         vec![13, 14, 15, 16]
    /// ]);
    ///
    /// let grid_slice = GridSlice::new(&grid, 1..=2, 1..=2).unwrap();
    /// let mut iter = grid_slice.iter();
    ///
    /// let mut row_iter = iter.next().unwrap();
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 0), &6)));
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(0, 1), &7)));
    /// assert_eq!(row_iter.next(), None);
    ///
    /// let mut row_iter = iter.next().unwrap();
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(1, 0), &10)));
    /// assert_eq!(row_iter.next(), Some((Coordinate::new(1, 1), &11)));
    /// assert_eq!(row_iter.next(), None);
    ///
    /// assert_eq!(iter.next(), None);
    /// ```
    fn iter<'a>(&'a self) -> GridIter<'a, Self, T>
    where
        T: 'a,
        Self: Sized,
    {
        GridIter::new(self, *self.row.start())
    }
}
