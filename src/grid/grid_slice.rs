use crate::coordinate_system::Coordinate;
use crate::grid::{Grid, GridIter};
use crate::{to_signed_coordinate, to_unsigned_coordinate};
use std::marker::PhantomData;
use std::ops::{Deref, RangeInclusive};

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
/// let grid = UnsizedGrid::from(vec![
///         vec![1,  2,  3,  4],
///         vec![5,  6,  7,  8],
///         vec![9,  10, 11, 12],
///         vec![13, 14, 15, 16]
/// ]);
///
/// let grid_slice = GridSlice::new(&grid, 1..=2, 1..=2).unwrap();
///
/// assert_eq!(grid_slice.get(&Coordinate::new(0, 0)), Some(&6));
/// assert_eq!(grid_slice.get(&Coordinate::new(1, 0)), Some(&10));
/// assert_eq!(grid_slice.get(&Coordinate::new(0, 1)), Some(&7));
/// assert_eq!(grid_slice.get(&Coordinate::new(1, 1)), Some(&11));
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
    /// let grid = UnsizedGrid::from(vec![
    ///         vec![1,  2,  3,  4],
    ///         vec![5,  6,  7,  8],
    ///         vec![9,  10, 11, 12],
    ///         vec![13, 14, 15, 16]
    /// ]);
    ///
    /// let grid_slice = GridSlice::new(&grid, 1..=2, 1..=2).unwrap();
    ///
    /// assert_eq!(grid_slice.get(&Coordinate::new(0, 0)), Some(&6));
    /// assert_eq!(grid_slice.get(&Coordinate::new(1, 0)), Some(&10));
    /// assert_eq!(grid_slice.get(&Coordinate::new(0, 1)), Some(&7));
    /// assert_eq!(grid_slice.get(&Coordinate::new(1, 1)), Some(&11));
    /// assert_eq!(grid_slice.get(&Coordinate::new(2, 0)), None);
    /// ```
    pub fn new(
        grid: &'grid G,
        row: RangeInclusive<usize>,
        col: RangeInclusive<usize>,
    ) -> Result<Self, ()> {
        if Self::is_valid_range(grid, row.clone(), col.clone()) {
            Ok(Self {
                grid,
                row,
                col,
                _marker: PhantomData,
            })
        } else {
            Err(())
        }
    }

    #[inline]
    fn is_valid_slice_row(&self, row: usize) -> bool {
        (0..self.num_rows()).contains(&row)
    }

    /// Check if the given range (row & col) is valid for the grid.
    #[inline]
    fn is_valid_range(grid: &G, row: RangeInclusive<usize>, col: RangeInclusive<usize>) -> bool
    where
        G: Grid<T>,
    {
        grid.is_valid_coordinate(&Coordinate::new(
            *row.start() as isize,
            *col.start() as isize,
        )) && grid.is_valid_coordinate(&Coordinate::new(*row.end() as isize, *col.end() as isize))
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
    /// use aoc_utils_rust::to_signed_coordinate;
    ///
    /// let grid = UnsizedGrid::from(vec![
    ///         vec![1,  2,  3,  4],
    ///         vec![5,  6,  7,  8],
    ///         vec![9,  10, 11, 12],
    ///         vec![13, 14, 15, 16]
    /// ]);
    ///
    ///  
    /// let _ = GridSlice::new(&grid, 1..=5, 1..=2).unwrap_err();
    ///
    ///  // [6,  7]
    ///  // [10, 11]
    ///  // [14, 15]
    /// let first_slice = GridSlice::new(&grid, 1..=3, 1..=2).unwrap();
    /// assert_eq!(first_slice.get(&to_signed_coordinate!(first_slice.bottom_right_coordinate())), Some(&15));
    ///
    ///
    ///  // [6,  7]
    ///  // [10, 11]
    /// let second_slice = GridSlice::from_slice(&first_slice, 0..=1, 0..=1).unwrap();
    /// assert_eq!(second_slice.get(&Coordinate::new(0, 0)), Some(&6));
    /// assert_eq!(second_slice.get(&to_signed_coordinate!(second_slice.bottom_right_coordinate())), Some(&11));
    ///
    ///  //  [11]
    ///  //  [15]
    /// let new_slice = GridSlice::from_slice(&first_slice, 1..=2, 1..=1).unwrap();
    ///
    /// assert_eq!(new_slice.get(&Coordinate::new(0, 0)), Some(&11));
    /// assert_eq!(new_slice.get(&Coordinate::new(1, 0)), Some(&15));
    /// assert_eq!(new_slice.get(&Coordinate::new(0, 1)), None);
    /// ```
    pub fn from_slice(
        slice: &GridSlice<'grid, G, T>,
        row: RangeInclusive<usize>,
        col: RangeInclusive<usize>,
    ) -> Result<Self, ()> {
        if Self::is_valid_range(slice.grid, row.clone(), col.clone()) {
            // Normalize the range relative to the underlying index of backing grid of the given slice
            let new_row = *slice.row.start() + *row.start()
                ..=*slice.row.start() + *row.start() + row.size_hint().0 - 1;
            let new_col = *slice.col.start() + *col.start()
                ..=*slice.col.start() + *col.start() + col.size_hint().0 - 1;
            Self::new(slice.grid, new_row, new_col)
        } else {
            Err(())
        }
    }
}

/// A type that represents an internal coordinate used to translate
/// to the actual coordinate of the backing grid
#[derive(Debug, Eq, PartialEq, Clone, Copy)]
#[repr(transparent)]
struct InternalCoordinate(Coordinate<usize>);

impl InternalCoordinate {
    fn from_slice_coordinate<G, T>(
        coordinate: &Coordinate<usize>,
        grid_slice: &GridSlice<G, T>,
    ) -> Self
    where
        G: Grid<T>,
    {
        let translated = Coordinate::new(
            coordinate.i + *grid_slice.row.start(),
            coordinate.j + *grid_slice.col.start(),
        );
        Self(translated)
    }

    fn to_slice_coordinate<G, T>(&self, grid_slice: &GridSlice<G, T>) -> Coordinate<usize>
    where
        G: Grid<T>,
    {
        Coordinate::new(
            self.0.i - *grid_slice.row.start(),
            self.0.j - *grid_slice.col.start(),
        )
    }
}

impl Deref for InternalCoordinate {
    type Target = Coordinate<usize>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'grid, G, T> Grid<T> for GridSlice<'grid, G, T>
where
    G: Grid<T>,
{
    /// Returns the number of rows in the grid slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::Grid;
    /// use aoc_utils_rust::grid::grid_slice::GridSlice;
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    ///
    /// let grid = UnsizedGrid::from(vec![
    ///         vec![1,  2,  3,  4],
    ///         vec![5,  6,  7,  8],
    ///         vec![9,  10, 11, 12],
    ///         vec![13, 14, 15, 16]
    /// ]);
    ///
    /// let grid_slice = GridSlice::new(&grid, 1..=3, 1..=2).unwrap();
    ///
    /// assert_eq!(grid_slice.num_rows(), 3);
    /// ```
    fn num_rows(&self) -> usize {
        self.row.size_hint().0
    }

    /// Returns the number of columns in the grid slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::Grid;
    /// use aoc_utils_rust::grid::grid_slice::GridSlice;
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    ///
    /// let grid = UnsizedGrid::from(vec![
    ///         vec![1,  2,  3,  4],
    ///         vec![5,  6,  7,  8],
    ///         vec![9,  10, 11, 12],
    ///         vec![13, 14, 15, 16]
    /// ]);
    ///
    /// let grid_slice = GridSlice::new(&grid, 1..=2, 1..=3).unwrap();
    ///
    /// assert_eq!(grid_slice.num_cols(), 3);
    /// ```
    fn num_cols(&self) -> usize {
        self.col.size_hint().0
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
    /// let grid = UnsizedGrid::from(vec![
    ///         vec![1,  2,  3,  4],
    ///         vec![5,  6,  7,  8],
    ///         vec![9,  10, 11, 12],
    ///         vec![13, 14, 15, 16]
    /// ]);
    ///
    /// let grid_slice = GridSlice::new(&grid, 1..=2, 1..=2).unwrap();
    ///
    /// assert_eq!(grid_slice.get_row(0), Some([6, 7].as_slice()));
    /// assert_eq!(grid_slice.get_row(1), Some([10, 11].as_slice()));
    /// ```
    fn get_row(&self, row: usize) -> Option<&[T]> {
        if self.is_valid_slice_row(row) {
            self.grid
                .get_row(
                    InternalCoordinate::from_slice_coordinate(&Coordinate::new(row, 0), self).i
                        as usize,
                )
                .map(|row| &row[self.col.clone()])
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
    /// let grid = UnsizedGrid::from(vec![
    ///         vec![1,  2,  3,  4],
    ///         vec![5,  6,  7,  8],
    ///         vec![9,  10, 11, 12],
    ///         vec![13, 14, 15, 16]
    /// ]);
    ///
    /// let grid_slice = GridSlice::new(&grid, 1..=2, 1..=2).unwrap();
    ///
    /// assert_eq!(grid_slice.get(&Coordinate::new(0, 0)), Some(&6));
    /// assert_eq!(grid_slice.get(&Coordinate::new(1, 0)), Some(&10));
    /// assert_eq!(grid_slice.get(&Coordinate::new(1, 1)), Some(&11));
    /// assert_eq!(grid_slice.get(&Coordinate::new(1, 2)), None);
    /// ```
    fn get(&self, coordinate: &Coordinate<isize>) -> Option<&T> {
        if !self.is_valid_coordinate(&coordinate) {
            return None;
        }
        self.grid.get(&to_signed_coordinate!(
            *InternalCoordinate::from_slice_coordinate(&to_unsigned_coordinate!(coordinate), self,)
        ))
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
    ///
    /// let grid = UnsizedGrid::from(vec![
    ///         vec![1,  2,  3,  4],
    ///         vec![5,  6,  7,  8],
    ///         vec![9,  10, 11, 12],
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
    #[inline]
    fn iter<'a>(&'a self) -> GridIter<'a, Self, T>
    where
        T: 'a,
        Self: Sized,
    {
        GridIter::new(self)
    }
}
