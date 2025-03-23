use crate::coordinate_system::Coordinate;
use crate::grid::GridMut;
use std::fmt::{Debug, Formatter};
use std::ops::Deref;

/// A timer struct used for setting up a new visitor.
#[repr(transparent)]
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Timer(u8);

impl Deref for Timer {
    type Target = u8;

    /// Dereferences the timer to get the underlying value.
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Timer {
    /// A constant representing a blank timer.
    pub const BLANK: Timer = Timer(0);

    /// Creates a new `Timer` instance with an initial value of 1.
    ///
    #[inline]
    const fn new() -> Self {
        Self(1)
    }

    /// Ticks the timer, incrementing its value by 1.
    ///
    /// If the value overflows, it returns an error and resets the timer.
    #[inline]
    fn tick(&mut self) -> Result<(), ()> {
        let res = self.wrapping_add(1);
        if res == 0 {
            *self = Self::new();
            Err(())
        } else {
            self.0 = res;
            Ok(())
        }
    }

    /// Resets the timer to the blank state.
    #[inline]
    fn reset(&mut self) {
        *self = Timer::BLANK;
    }
}

/// A struct representing a visitor that operates on a grid.
///
/// # Type Parameters
/// * `G` - The type of the backing grid.
#[derive(Clone)]
pub struct TheVisitor<G> {
    backing_grid: G,
    curr_time: Timer,
}

impl<G> TheVisitor<G>
where
    G: GridMut<Timer>,
{
    /// Creates a new `TheVisitor` instance with the given backing grid.
    ///
    /// # Arguments
    /// * `backing_grid` - The grid to be used as the backing grid.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::grid::sized_grid::SizedGrid;
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    /// use aoc_utils_rust::miscellaneous::the_visitor::{TheVisitor, Timer};
    ///
    /// let grid = UnsizedGrid::from(vec![vec![Timer::BLANK; 4]; 4]);
    /// let visitor = TheVisitor::new(grid);
    ///
    /// let grid = SizedGrid::<Timer, 4, 4>::new(Timer::BLANK);
    /// let visitor = TheVisitor::new(grid);
    /// ```
    #[inline]
    pub const fn new(backing_grid: G) -> Self {
        Self {
            backing_grid,
            curr_time: Timer::new(),
        }
    }

    /// Clears the visitor, incrementing the timer. If the timer overflows, the grid is reset.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::sized_grid::SizedGrid;
    /// use aoc_utils_rust::miscellaneous::the_visitor::{TheVisitor, Timer};
    ///
    /// let grid = SizedGrid::<Timer, 4, 4>::new(Timer::BLANK);
    /// let mut visitor = TheVisitor::new(grid);
    ///
    /// for _ in 0..u16::MAX { // Simulate a lot of clearing
    ///     visitor.mark_visited(Coordinate::new(1, 1));
    ///     assert!(visitor.has_visited(Coordinate::new(1, 1)));
    ///     visitor.clear();
    ///     assert!(!visitor.has_visited(Coordinate::new(1, 1)));
    ///     visitor.clear();
    /// }
    ///
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        if self.curr_time.tick().is_err() {
            self.reset_grid();
        }
    }

    /// Marks the specified coordinate as visited.
    ///
    /// # Arguments
    /// * `coord` - The coordinate to mark as visited.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    /// use aoc_utils_rust::miscellaneous::the_visitor::TheVisitor;
    /// use aoc_utils_rust::miscellaneous::the_visitor::Timer;
    ///
    /// let mut grid = UnsizedGrid::from(vec![vec![Timer::BLANK; 4]; 4]);
    /// let mut visitor = TheVisitor::new(grid);
    /// visitor.mark_visited(Coordinate::new(1, 1));
    /// ```
    #[inline]
    pub fn mark_visited(&mut self, coord: Coordinate<isize>) -> bool {
        if !self.has_visited(coord) {
            *self.backing_grid.get_mut(&coord).unwrap() = self.curr_time;
            true
        } else {
            false
        }
    }

    /// Unmarks the specified coordinate as visited by resetting the timer at that coordinate.
    ///
    /// # Arguments
    /// * `coord` - The coordinate to unmark as visited.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::sized_grid::SizedGrid;
    /// use aoc_utils_rust::miscellaneous::the_visitor::{TheVisitor, Timer};
    ///
    /// let mut grid = SizedGrid::from([[Timer::BLANK; 4]; 4]);
    /// let mut visitor = TheVisitor::new(grid);
    /// visitor.mark_visited(Coordinate::new(1, 1));
    /// assert!(visitor.has_visited(Coordinate::new(1, 1)));
    /// visitor.unmark_visited(Coordinate::new(1, 1));
    /// assert!(!visitor.has_visited(Coordinate::new(1, 1)));
    /// ```
    pub fn unmark_visited(&mut self, coord: Coordinate<isize>) {
        self.backing_grid.get_mut(&coord).unwrap().reset();
    }

    /// Checks if the specified coordinate has been visited.
    ///
    /// # Arguments
    /// * `coord` - The coordinate to check.
    ///
    /// # Returns
    /// `true` if the coordinate has been visited, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::coordinate_system::Coordinate;
    /// use aoc_utils_rust::grid::unsized_grid::UnsizedGrid;
    /// use aoc_utils_rust::miscellaneous::the_visitor::TheVisitor;
    /// use aoc_utils_rust::miscellaneous::the_visitor::Timer;
    ///
    /// let mut grid = UnsizedGrid::from(vec![vec![Timer::BLANK; 4]; 4]);
    /// let mut visitor = TheVisitor::new(grid);
    /// visitor.mark_visited(Coordinate::new(1, 1));
    /// assert!(visitor.has_visited(Coordinate::new(1, 1)));
    /// assert!(!visitor.has_visited(Coordinate::new(0, 0)));
    /// ```
    #[inline]
    pub fn has_visited(&self, coord: Coordinate<isize>) -> bool {
        *self.backing_grid.get(&coord).unwrap() == self.curr_time
    }

    fn reset_grid(&mut self) {
        self.backing_grid
            .iter_mut()
            .for_each(|row| row.for_each(|(_, timer)| timer.reset()));
    }
}

impl<G: GridMut<Timer>> Debug for TheVisitor<G> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for row in self.backing_grid.iter() {
            for (coord, timer) in row {
                write!(
                    f,
                    "({},{})|{} ",
                    coord.i,
                    coord.j,
                    if *timer == self.curr_time { "x" } else { "_" }
                )?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}
