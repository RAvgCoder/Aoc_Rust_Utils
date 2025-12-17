use crate::coordinate_system::direction::Direction;
use num_traits::{ConstZero, Num, NumCast, Signed};
use std::fmt;
use std::num::ParseIntError;
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};
use std::str::FromStr;

/// # Coordinate System
///
/// This module provides the `Coordinate` struct for representing coordinates in a 2D grid,
/// along with operations for manipulating these coordinates. It also includes integration
/// with `Direction` and `FullDirection` enums for directional operations.
///
/// # Examples
///
/// Basic usage of `Coordinate`:
/// ```
/// use self::aoc_utils_rust::coordinate_system::Coordinate;
/// let coord = Coordinate::new(3, 4);
/// assert_eq!(coord.i, 3);
/// assert_eq!(coord.j, 4);
/// ```
///
/// Calculating Manhattan distance:
/// ```
/// use self::aoc_utils_rust::coordinate_system::Coordinate;
/// let coord = Coordinate::new(3, 4);
/// let origin = Coordinate::new(0, 0);
/// assert_eq!(coord.manhattan_distance(origin), 7);
/// ```
///
/// Transposing coordinates:
/// ```
/// use self::aoc_utils_rust::coordinate_system::Coordinate;
/// let coord = Coordinate::new(3, 4);
/// let transposed = coord.transpose();
/// assert_eq!(transposed.i, 4);
/// assert_eq!(transposed.j, 3);
/// ```
///
/// Adding coordinates:
/// ```
/// use self::aoc_utils_rust::coordinate_system::Coordinate;
/// let coord1 = Coordinate::new(3, 4);
/// let coord2 = Coordinate::new(1, 2);
/// let result = coord1 + coord2;
/// assert_eq!(result.i, 4);
/// assert_eq!(result.j, 6);
/// ```
///
/// Integration with `Direction`:
/// ```
/// use self::aoc_utils_rust::coordinate_system::Coordinate;
/// use self::aoc_utils_rust::coordinate_system::direction::Direction;
/// let coord = Coordinate::new(3, 4);
/// let north_offset = coord + Direction::North;
/// assert_eq!(north_offset.i, 2);
/// assert_eq!(north_offset.j, 4);
/// ```
///
/// Integration with `FullDirection`:
/// ```
/// use self::aoc_utils_rust::coordinate_system::Coordinate;
/// use self::aoc_utils_rust::coordinate_system::direction::FullDirection;
/// let coord = Coordinate::new(3, 4);
/// let northeast_offset = coord + FullDirection::NorthEast;
/// assert_eq!(northeast_offset.i, 2);
/// assert_eq!(northeast_offset.j, 5);
/// ```
#[derive(Default, Clone, Copy, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub struct Coordinate<Ty = i32>
where
    Ty: Num + NumCast,
{
    pub i: Ty,
    pub j: Ty,
}

impl<Ty> Coordinate<Ty>
where
    Ty: Num + NumCast + ConstZero,
{
    pub const ORIGIN: Coordinate<Ty> = Coordinate {
        i: Ty::ZERO,
        j: Ty::ZERO,
    };
}

impl<Ty> Coordinate<Ty>
where
    Ty: Copy + fmt::Debug + fmt::Display + Num + NumCast,
{
    /// Creates a new `Coordinate`.
    ///
    /// # Arguments
    ///
    /// * `x` - The x-coordinate.
    /// * `y` - The y-coordinate.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// let coord = Coordinate::new(3, 4);
    /// assert_eq!(coord.i, 3);
    /// assert_eq!(coord.j, 4);
    /// ```
    #[inline(always)]
    pub const fn new(x: Ty, y: Ty) -> Self {
        Self { i: x, j: y }
    }

    /// Calculates the Manhattan distance between two coordinates.
    ///
    /// # Arguments
    ///
    /// * `other` - The other coordinate to calculate the distance to.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// let coord1 = Coordinate::new(3, 4);
    /// let coord2 = Coordinate::new(1, 1);
    /// assert_eq!(coord1.manhattan_distance(coord2), 5);
    ///
    /// let coord1 = Coordinate::new(3, 4);
    /// let coord2 = Coordinate::new(0, 0);
    /// assert_eq!(coord1.manhattan_distance(coord2), 7);
    /// ```
    #[inline]
    pub fn manhattan_distance(&self, other: Self) -> Ty
    where
        Ty: Signed,
    {
        let (dx, dy) = self.slope_relative(other);
        dx.abs() + dy.abs()
    }

    /// Calculates the Euclidean distance between two coordinates.
    ///
    /// # Arguments
    ///
    /// * `other` - The other coordinate to calculate the distance to.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// let coord1 = Coordinate::new(3, 4);
    /// let coord2 = Coordinate::new(0, 0);
    /// assert_eq!(coord1.distance_to(coord2), 5.0);
    /// ```
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// let coord1 = Coordinate::new(1, 1);
    /// let coord2 = Coordinate::new(4, 5);
    /// assert_eq!(coord1.distance_to(coord2), 5.0);
    /// ```
    #[inline]
    pub fn distance_to(&self, other: Self) -> f64 {
        let (dx, dy) = self.slope_relative(other);
        Self::f64_cast(dx * dx + dy * dy).sqrt()
    }

    #[inline(always)]
    fn f64_cast(ty: Ty) -> f64 {
        ty.to_f64().expect("Cannot convert to f64")
    }

    /// Transposes the coordinate.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// let coord = Coordinate::new(3, 4);
    /// let transposed = coord.transpose();
    /// assert_eq!(transposed.i, 4);
    /// assert_eq!(transposed.j, 3);
    /// ```
    #[inline(always)]
    pub const fn transpose(&self) -> Self {
        Self::new(self.j, self.i)
    }

    /// Calculates the relative slope between two coordinates.
    ///
    /// The slope is represented as a tuple of integers `(di, dj)` || `(rise, run)`, where `di` and `dj`
    /// are the differences in the x and y coordinates, respectively.
    ///
    /// # Arguments
    ///
    /// * `self` - The starting coordinate.
    /// * `other` - The ending coordinate.
    ///
    /// # Returns
    ///
    /// A tuple `(di, dj)` representing the slope.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// let coord1 = Coordinate::new(4, 4);
    /// let coord2 = Coordinate::new(1, 8);
    /// assert_eq!(coord2.slope_relative(coord1), (3, -4));
    /// assert_eq!(coord1.slope_relative(coord2), (-3, 4));
    /// ```
    #[inline(always)]
    pub fn slope_relative(&self, other: Self) -> (Ty, Ty) {
        let di = other.i - self.i; // Difference in x-coordinates
        let dj = other.j - self.j; // Difference in y-coordinates
        (di, dj) // Return the slope as a tuple
    }

    /// Calculates the slope between two coordinates.
    ///
    /// The slope is represented as a floating-point number. If the difference in x-coordinates (`dx`) is zero,
    /// the function returns `f64::INFINITY` to represent an infinite slope.
    ///
    /// # Arguments
    ///
    /// * `self` - The starting coordinate.
    /// * `other` - The ending coordinate.
    ///
    /// # Returns
    ///
    /// A floating-point number representing the slope.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// let coord1 = Coordinate::new(3, 4);
    /// let coord2 = Coordinate::new(6, 8);
    /// assert_eq!(coord1.slope(coord2), Some(4.0 / 3.0));
    /// ```
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// let coord1 = Coordinate::new(1, 1);
    /// let coord2 = Coordinate::new(1, 5);
    /// assert_eq!(coord1.slope(coord2), None);
    /// ```
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// let coord1 = Coordinate::new(0, 0);
    /// let coord2 = Coordinate::new(4, 2);
    /// assert_eq!(coord1.slope(coord2), Some(0.5));
    /// ```
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// let coord1 = Coordinate::new(2, 3);
    /// let coord2 = Coordinate::new(5, 3);
    /// assert_eq!(coord1.slope(coord2), Some(0.0));
    /// ```
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// let coord1 = Coordinate::new(3, 4);
    /// let coord2 = Coordinate::new(0, 0);
    /// assert_eq!(coord1.slope(coord2), Some(4.0 / 3.0));
    /// ```
    #[inline(always)]
    pub fn slope(&self, other: Self) -> Option<f64> {
        let (dx, dy) = self.slope_relative(other);
        if dx.is_zero() {
            None
        } else {
            Some(Self::f64_cast(dy) / Self::f64_cast(dx))
        }
    }
}

#[macro_export]
macro_rules! to_unsigned_coordinate {
    ($coord:expr) => {
        Coordinate::<usize> {
            i: $coord.i as usize,
            j: $coord.j as usize,
        }
    };
}

#[macro_export]
macro_rules! to_signed_coordinate {
    ($coord:expr) => {
        Coordinate::<isize> {
            i: $coord.i as isize,
            j: $coord.j as isize,
        }
    };
}

impl From<Coordinate<isize>> for Coordinate<usize> {
    fn from(coord: Coordinate<isize>) -> Self {
        Coordinate {
            i: coord.i as usize,
            j: coord.j as usize,
        }
    }
}

impl From<Coordinate<usize>> for Coordinate<isize> {
    fn from(coord: Coordinate<usize>) -> Self {
        Coordinate {
            i: coord.i as isize,
            j: coord.j as isize,
        }
    }
}

impl AddAssign for Coordinate {
    /// Adds another `Coordinate` to this one.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// let mut coord1 = Coordinate::new(3, 4);
    /// let coord2 = Coordinate::new(1, 2);
    /// coord1 += coord2;
    /// assert_eq!(coord1.i, 4);
    /// assert_eq!(coord1.j, 6);
    /// ```
    fn add_assign(&mut self, other: Self) {
        self.i += other.i;
        self.j += other.j;
    }
}

impl<Ty> AddAssign<Direction> for Coordinate<Ty>
where
    Ty: Num + NumCast + Copy,
{
    /// Adds a `Direction` to this `Coordinate`.
    ///
    /// For unsigned types, panics if the resulting coordinate would have negative values.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// use self::aoc_utils_rust::coordinate_system::direction::Direction;
    /// let mut coord = Coordinate::new(3, 4);
    /// coord += Direction::North;
    /// assert_eq!(coord.i, 2);
    /// assert_eq!(coord.j, 4);
    /// ```
    ///
    /// Works with unsigned types:
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// use self::aoc_utils_rust::coordinate_system::direction::Direction;
    /// let mut coord = Coordinate::new(3usize, 4usize);
    /// coord += Direction::East;
    /// assert_eq!(coord.i, 3);
    /// assert_eq!(coord.j, 5);
    /// ```
    #[inline(always)]
    fn add_assign(&mut self, direction: Direction) {
        let (dx, dy) = direction.offset();
        let i_isize = self.i.to_isize().expect("Cannot convert i to isize");
        let j_isize = self.j.to_isize().expect("Cannot convert j to isize");
        self.i = Ty::from(i_isize + dx as isize).expect("Coordinate overflow in i");
        self.j = Ty::from(j_isize + dy as isize).expect("Coordinate overflow in j");
    }
}

impl<Ty> AddAssign<direction::FullDirection> for Coordinate<Ty>
where
    Ty: Num + NumCast + Copy,
{
    /// Adds a `FullDirection` to this `Coordinate`.
    ///
    /// For unsigned types, panics if the resulting coordinate would have negative values.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// use self::aoc_utils_rust::coordinate_system::direction::FullDirection;
    /// let mut coord = Coordinate::new(5, 5);
    /// coord += FullDirection::NorthWest;
    /// assert_eq!(coord.i, 4);
    /// assert_eq!(coord.j, 4);
    /// ```
    ///
    /// Works with unsigned types:
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// use self::aoc_utils_rust::coordinate_system::direction::FullDirection;
    /// let mut coord = Coordinate::new(3usize, 4usize);
    /// coord += FullDirection::NorthEast;
    /// assert_eq!(coord.i, 2);
    /// assert_eq!(coord.j, 5);
    /// ```
    #[inline(always)]
    fn add_assign(&mut self, direction: direction::FullDirection) {
        let (dx, dy) = direction.offset();
        let i_isize = self.i.to_isize().expect("Cannot convert i to isize");
        let j_isize = self.j.to_isize().expect("Cannot convert j to isize");
        self.i = Ty::from(i_isize + dx as isize).expect("Coordinate overflow in i");
        self.j = Ty::from(j_isize + dy as isize).expect("Coordinate overflow in j");
    }
}

impl Add for Coordinate {
    type Output = Self;
    /// Adds two `Coordinate` values.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// let coord1 = Coordinate::new(3, 4);
    /// let coord2 = Coordinate::new(1, 2);
    /// let result = coord1 + coord2;
    /// assert_eq!(result.i, 4);
    /// assert_eq!(result.j, 6);
    /// ```
    fn add(self, other: Self) -> Self::Output {
        Self {
            i: self.i + other.i,
            j: self.j + other.j,
        }
    }
}

impl Sub for Coordinate {
    type Output = Self;

    /// Subtracts one `Coordinate` from another.
    ///
    /// # Arguments
    ///
    /// * `rhs` - The right-hand side `Coordinate` to subtract.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// let coord1 = Coordinate::new(5, 7);
    /// let coord2 = Coordinate::new(2, 3);
    /// let result = coord1 - coord2;
    /// assert_eq!(result.i, 3);
    /// assert_eq!(result.j, 4);
    /// ```
    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            i: self.i - rhs.i,
            j: self.j - rhs.j,
        }
    }
}
impl<Ty> SubAssign for Coordinate<Ty>
where
    Ty: SubAssign + NumCast + Num,
{
    /// Subtracts another `Coordinate` from this one.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// let mut coord1 = Coordinate::new(5usize, 7usize);
    /// let coord2 = Coordinate::new(2usize, 3usize);
    /// coord1 -= coord2;
    /// assert_eq!(coord1.i, 3);
    /// assert_eq!(coord1.j, 4);
    /// ```
    fn sub_assign(&mut self, rhs: Self) {
        self.i -= rhs.i;
        self.j -= rhs.j;
    }
}

impl<Ty> Add<Direction> for Coordinate<Ty>
where
    Ty: Num + NumCast + Copy,
{
    type Output = Self;

    /// Adds a `Direction` to the `Coordinate`.
    ///
    /// For unsigned types, panics if the resulting coordinate would have negative values.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// use self::aoc_utils_rust::coordinate_system::direction::Direction;
    /// let coord = Coordinate::new(3, 4);
    /// let north_offset = coord + Direction::North;
    /// assert_eq!(north_offset.i, 2);
    /// assert_eq!(north_offset.j, 4);
    /// ```
    ///
    /// Works with unsigned types:
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// use self::aoc_utils_rust::coordinate_system::direction::Direction;
    /// let coord = Coordinate::new(3usize, 4usize);
    /// let south_offset = coord + Direction::South;
    /// assert_eq!(south_offset.i, 4);
    /// assert_eq!(south_offset.j, 4);
    /// ```
    fn add(self, direction: Direction) -> Self::Output {
        let (dx, dy) = direction.offset();
        let i_isize = self.i.to_isize().expect("Cannot convert i to isize");
        let j_isize = self.j.to_isize().expect("Cannot convert j to isize");
        Self {
            i: Ty::from(i_isize + dx as isize).expect("Coordinate overflow in i"),
            j: Ty::from(j_isize + dy as isize).expect("Coordinate overflow in j"),
        }
    }
}

impl<Ty> Mul<Ty> for Coordinate<Ty>
where
    Ty: NumCast + Num + Mul + Copy,
{
    type Output = Coordinate<Ty>;

    /// Multiplies the `Coordinate` by a scalar value.
    ///
    /// # Arguments
    ///
    /// * `rhs` - The scalar value to multiply by.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// let coord = Coordinate::new(3usize, 4);
    /// let result = coord * 2;
    /// assert_eq!(result.i, 6);
    /// assert_eq!(result.j, 8);
    /// ```
    fn mul(self, rhs: Ty) -> Self::Output {
        Self {
            i: self.i * rhs,
            j: self.j * rhs,
        }
    }
}

impl<Ty> MulAssign<Ty> for Coordinate<Ty>
where
    Ty: NumCast + Num + MulAssign + Copy,
{
    /// Multiplies the `Coordinate` by a scalar value in place.
    ///
    /// # Arguments
    ///
    /// * `rhs` - The scalar value to multiply by.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// let mut coord = Coordinate::new(3f32, 4f32);
    /// coord *= 2f32;
    /// assert_eq!(coord.i, 6f32);
    /// assert_eq!(coord.j, 8f32);
    /// ```
    fn mul_assign(&mut self, rhs: Ty) {
        self.i *= rhs;
        self.j *= rhs;
    }
}

impl<Ty> From<(Ty, Ty)> for Coordinate<Ty>
where
    Ty: Copy + fmt::Debug + fmt::Display + Num + NumCast + Signed,
{
    /// Creates a `Coordinate` from a tuple.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// let coord: Coordinate = (3, 4).into();
    /// assert_eq!(coord.i, 3);
    /// assert_eq!(coord.j, 4);
    /// ```
    #[inline(always)]
    fn from((i, j): (Ty, Ty)) -> Self {
        Self::new(i, j)
    }
}

impl<Ty> Into<(Ty, Ty)> for Coordinate<Ty>
where
    Ty: Copy + fmt::Debug + fmt::Display + Num + NumCast + Signed,
{
    /// Converts a `Coordinate` into a tuple.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// let coord = Coordinate::new(3, 4);
    /// let tuple: (i32, i32) = coord.into();
    /// assert_eq!(tuple, (3, 4));
    /// ```
    #[inline(always)]
    fn into(self) -> (Ty, Ty) {
        (self.i, self.j)
    }
}

impl<Ty> Add<direction::FullDirection> for Coordinate<Ty>
where
    Ty: Num + NumCast + Copy,
{
    type Output = Self;

    /// Adds a `FullDirection` to the `Coordinate`.
    ///
    /// For unsigned types, panics if the resulting coordinate would have negative values.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// use self::aoc_utils_rust::coordinate_system::direction::FullDirection;
    /// let coord = Coordinate::new(3, 4);
    /// let northeast_offset = coord + FullDirection::NorthEast;
    /// assert_eq!(northeast_offset.i, 2);
    /// assert_eq!(northeast_offset.j, 5);
    /// ```
    ///
    /// Works with unsigned types:
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// use self::aoc_utils_rust::coordinate_system::direction::FullDirection;
    /// let coord = Coordinate::new(10usize, 10usize);
    /// let southwest_offset = coord + FullDirection::SouthWest;
    /// assert_eq!(southwest_offset.i, 11);
    /// assert_eq!(southwest_offset.j, 9);
    /// ```
    fn add(self, direction: direction::FullDirection) -> Self::Output {
        let (dx, dy) = direction.offset();
        let i_isize = self.i.to_isize().expect("Cannot convert i to isize");
        let j_isize = self.j.to_isize().expect("Cannot convert j to isize");
        Self {
            i: Ty::from(i_isize + dx as isize).expect("Coordinate overflow in i"),
            j: Ty::from(j_isize + dy as isize).expect("Coordinate overflow in j"),
        }
    }
}

impl<Ty> fmt::Debug for Coordinate<Ty>
where
    Ty: Num + NumCast + fmt::Debug + fmt::Display,
{
    /// Formats the `Coordinate` using the given formatter.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// let coord = Coordinate::new(3, 4);
    /// assert_eq!(format!("{:?}", coord), "Coordinate(3, 4)");
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Coordinate({}, {})", self.i, self.j)
    }
}

impl<Ty: FromStr<Err = ParseIntError>> FromStr for Coordinate<Ty>
where
    Ty: Copy + fmt::Debug + fmt::Display + Num + NumCast + Signed,
{
    type Err = String;

    /// Implements the `FromStr` trait for the `Coordinate` struct, allowing it to be created from a string representation.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// use std::str::FromStr;
    /// let coord: Coordinate<i8> = Coordinate::from_str("3,4").unwrap();
    /// assert_eq!(coord.i, 3);
    /// assert_eq!(coord.j, 4);
    /// ```
    fn from_str(line: &str) -> Result<Self, Self::Err> {
        match line.split_once(',') {
            None => Err(format!("Invalid coordinate `{}`. Format is 'x,y'", line)),
            Some((i, j)) => {
                let x = i
                    .parse()
                    .map_err(|err| format!("Cannot parse i axis: {}", err))?;
                let y = j
                    .parse()
                    .map_err(|err| format!("Cannot parse j axis: {}", err))?;
                Ok(Self::new(x, y))
            }
        }
    }
}

/// This module provides the `Direction` and `FullDirection` enums for representing directions
/// in a 2D grid, along with operations for manipulating these directions.
///
/// # Examples
///
/// Basic usage of `Direction`:
/// ```
/// use self::aoc_utils_rust::coordinate_system::direction::Direction;
/// let north = Direction::North;
/// assert_eq!(north.offset(), (-1, 0));
/// ```
///
/// Basic usage of `FullDirection`:
/// ```
/// use self::aoc_utils_rust::coordinate_system::direction::FullDirection;
/// let northeast = FullDirection::NorthEast;
/// assert_eq!(northeast.offset(), (-1, 1));
/// ```
pub mod direction {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub enum Direction {
        North,
        East,
        South,
        West,
        Current,
    }

    impl Direction {
        /// Returns the offset for the direction.
        ///
        /// # Examples
        ///
        /// ```
        /// use self::aoc_utils_rust::coordinate_system::direction::Direction;
        /// let north = Direction::North;
        /// assert_eq!(north.offset(), (-1, 0));
        /// ```
        pub const fn offset(&self) -> (i8, i8) {
            match self {
                Self::North => (-1, 0),
                Self::East => (0, 1),
                Self::South => (1, 0),
                Self::West => (0, -1),
                Self::Current => (0, 0),
            }
        }

        /// Returns an array containing the four cardinal directions.
        ///
        /// # Returns
        /// An array of `Direction` enums representing the four cardinal directions:
        /// North, East, South, and West.
        ///
        /// # Examples
        ///
        /// ```
        /// use self::aoc_utils_rust::coordinate_system::direction::Direction;
        /// let directions = Direction::direction_list();
        /// assert_eq!(directions, [Direction::North, Direction::East, Direction::South, Direction::West]);
        /// ```
        pub const fn direction_list() -> [Direction; 4] {
            [Self::North, Self::East, Self::South, Self::West]
        }

        /// Rotates the direction 90 degrees to the right.
        ///
        /// # Examples
        ///
        /// ```
        /// use self::aoc_utils_rust::coordinate_system::direction::Direction;
        /// assert_eq!(Direction::North.rotate_90(), Direction::East);
        /// assert_eq!(Direction::East.rotate_90(), Direction::South);
        /// assert_eq!(Direction::South.rotate_90(), Direction::West);
        /// assert_eq!(Direction::West.rotate_90(), Direction::North);
        /// assert_eq!(Direction::Current.rotate_90(), Direction::Current);
        /// ```
        pub const fn rotate_90(&self) -> Direction {
            match self {
                Self::North => Self::East,
                Self::East => Self::South,
                Self::South => Self::West,
                Self::West => Self::North,
                Self::Current => Self::Current,
            }
        }

        /// Rotates the direction 90 degrees to the left.
        ///
        /// # Examples
        ///
        /// ```
        /// use self::aoc_utils_rust::coordinate_system::direction::Direction;
        /// assert_eq!(Direction::North.rotate_270(), Direction::West);
        /// assert_eq!(Direction::East.rotate_270(), Direction::North);
        /// assert_eq!(Direction::South.rotate_270(), Direction::East);
        /// assert_eq!(Direction::West.rotate_270(), Direction::South);
        /// assert_eq!(Direction::Current.rotate_270(), Direction::Current);
        /// ```
        pub const fn rotate_270(&self) -> Direction {
            match self {
                Self::North => Self::West,
                Self::East => Self::North,
                Self::South => Self::East,
                Self::West => Self::South,
                Self::Current => Self::Current,
            }
        }

        /// Returns the opposite direction.
        ///
        /// # Examples
        ///
        /// ```
        /// use self::aoc_utils_rust::coordinate_system::direction::Direction;
        /// assert_eq!(Direction::North.rotate_180(), Direction::South);
        /// assert_eq!(Direction::East.rotate_180(), Direction::West);
        /// assert_eq!(Direction::South.rotate_180(), Direction::North);
        /// assert_eq!(Direction::West.rotate_180(), Direction::East);
        /// assert_eq!(Direction::Current.rotate_180(), Direction::Current);
        /// ```
        pub const fn rotate_180(&self) -> Direction {
            match self {
                Self::North => Self::South,
                Self::East => Self::West,
                Self::South => Self::North,
                Self::West => Self::East,
                Self::Current => Self::Current,
            }
        }
    }

    impl TryFrom<char> for Direction {
        type Error = &'static str;

        /// Tries to convert a character into a `Direction`.
        ///
        /// # Examples
        ///
        /// ```
        /// use self::aoc_utils_rust::coordinate_system::direction::Direction;
        /// let direction = Direction::try_from('N').unwrap();
        /// assert_eq!(direction, Direction::North);
        /// ```
        fn try_from(value: char) -> Result<Self, Self::Error> {
            match value {
                'N' => Ok(Self::North),
                'E' => Ok(Self::East),
                'S' => Ok(Self::South),
                'W' => Ok(Self::West),
                _ => Err("Invalid direction"),
            }
        }
    }

    impl TryFrom<(i8, i8)> for Direction {
        type Error = &'static str;

        fn try_from(value: (i8, i8)) -> Result<Self, Self::Error> {
            match value {
                (-1, 0) => Ok(Self::North),
                (0, 1) => Ok(Self::East),
                (1, 0) => Ok(Self::South),
                (0, -1) => Ok(Self::West),
                (0, 0) => Ok(Self::Current),
                _ => Err("Invalid direction pair"),
            }
        }
    }

    /// Represents the eight cardinal and inter cardinal directions, plus the current position.
    ///
    /// # Examples
    ///
    /// Basic usage of `FullDirection`:
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::direction::FullDirection;
    /// let northeast = FullDirection::NorthEast;
    /// assert_eq!(northeast.offset(), (-1, 1));
    /// ```
    ///
    /// Listing all full directions:
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::direction::FullDirection;
    /// let directions = FullDirection::full_direction_list();
    /// assert_eq!(directions, [
    ///     FullDirection::North,
    ///     FullDirection::NorthEast,
    ///     FullDirection::East,
    ///     FullDirection::SouthEast,
    ///     FullDirection::South,
    ///     FullDirection::SouthWest,
    ///     FullDirection::West,
    ///     FullDirection::NorthWest,
    /// ]);
    /// ```
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub enum FullDirection {
        North,
        NorthEast,
        East,
        SouthEast,
        South,
        SouthWest,
        West,
        NorthWest,
        Current,
    }

    impl FullDirection {
        /// Returns the offset for the full direction.
        ///
        /// # Examples
        ///
        /// ```
        /// use self::aoc_utils_rust::coordinate_system::direction::FullDirection;
        /// let northeast = FullDirection::NorthEast;
        /// assert_eq!(northeast.offset(), (-1, 1));
        /// ```
        pub const fn offset(&self) -> (i8, i8) {
            match self {
                Self::North => Direction::North.offset(),
                Self::NorthEast => (-1, 1),
                Self::East => Direction::East.offset(),
                Self::SouthEast => (1, 1),
                Self::South => Direction::South.offset(),
                Self::SouthWest => (1, -1),
                Self::West => Direction::West.offset(),
                Self::NorthWest => (-1, -1),
                Self::Current => Direction::Current.offset(),
            }
        }

        /// Returns an array containing the eight full cardinal and intercardinal directions.
        ///
        /// # Returns
        /// An array of `FullDirection` enums representing the eight full directions:
        /// North, NorthEast, East, SouthEast, South, SouthWest, West, and NorthWest.
        ///
        /// # Examples
        ///
        /// ```
        /// use self::aoc_utils_rust::coordinate_system::direction::FullDirection;
        /// let directions = FullDirection::full_direction_list();
        /// assert_eq!(directions, [
        ///     FullDirection::North,
        ///     FullDirection::NorthEast,
        ///     FullDirection::East,
        ///     FullDirection::SouthEast,
        ///     FullDirection::South,
        ///     FullDirection::SouthWest,
        ///     FullDirection::West,
        ///     FullDirection::NorthWest,
        /// ]);
        /// ```
        pub const fn full_direction_list() -> [FullDirection; 8] {
            [
                Self::North,
                Self::NorthEast,
                Self::East,
                Self::SouthEast,
                Self::South,
                Self::SouthWest,
                Self::West,
                Self::NorthWest,
            ]
        }
    }

    impl TryFrom<&str> for FullDirection {
        type Error = &'static str;

        /// Tries to convert a string slice into a `FullDirection`.
        ///
        /// # Examples
        ///
        /// ```
        /// use self::aoc_utils_rust::coordinate_system::direction::FullDirection;
        /// let direction = FullDirection::try_from("NE").unwrap();
        /// assert_eq!(direction, FullDirection::NorthEast);
        /// ```
        fn try_from(value: &str) -> Result<Self, Self::Error> {
            match value {
                "N" => Ok(Self::North),
                "NE" => Ok(Self::NorthEast),
                "E" => Ok(Self::East),
                "SE" => Ok(Self::SouthEast),
                "S" => Ok(Self::South),
                "SW" => Ok(Self::SouthWest),
                "W" => Ok(Self::West),
                "NW" => Ok(Self::NorthWest),
                _ => Err("Invalid direction"),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add_assign_direction_signed_types() {
        let mut coord_i32 = Coordinate::new(10i32, 20i32);
        coord_i32 += Direction::North;
        assert_eq!(coord_i32.i, 9);
        assert_eq!(coord_i32.j, 20);

        let mut coord_i64 = Coordinate::new(100i64, 200i64);
        coord_i64 += Direction::East;
        assert_eq!(coord_i64.i, 100);
        assert_eq!(coord_i64.j, 201);

        let mut coord_isize = Coordinate::new(50isize, 75isize);
        coord_isize += Direction::South;
        assert_eq!(coord_isize.i, 51);
        assert_eq!(coord_isize.j, 75);

        let mut coord_i16 = Coordinate::new(15i16, 25i16);
        coord_i16 += Direction::West;
        assert_eq!(coord_i16.i, 15);
        assert_eq!(coord_i16.j, 24);
    }

    #[test]
    fn test_add_assign_direction_unsigned_types() {
        let mut coord_usize = Coordinate::new(10usize, 20usize);
        coord_usize += Direction::South;
        assert_eq!(coord_usize.i, 11);
        assert_eq!(coord_usize.j, 20);

        let mut coord_u32 = Coordinate::new(100u32, 200u32);
        coord_u32 += Direction::East;
        assert_eq!(coord_u32.i, 100);
        assert_eq!(coord_u32.j, 201);

        let mut coord_u64 = Coordinate::new(500u64, 750u64);
        coord_u64 += Direction::West;
        assert_eq!(coord_u64.i, 500);
        assert_eq!(coord_u64.j, 749);

        let mut coord_u16 = Coordinate::new(15u16, 25u16);
        coord_u16 += Direction::North;
        assert_eq!(coord_u16.i, 14);
        assert_eq!(coord_u16.j, 25);
    }

    #[test]
    fn test_add_direction_signed_types() {
        let coord_i32 = Coordinate::new(10i32, 20i32);
        let result = coord_i32 + Direction::North;
        assert_eq!(result.i, 9);
        assert_eq!(result.j, 20);

        let coord_i64 = Coordinate::new(100i64, 200i64);
        let result = coord_i64 + Direction::West;
        assert_eq!(result.i, 100);
        assert_eq!(result.j, 199);

        let coord_isize = Coordinate::new(50isize, 75isize);
        let result = coord_isize + Direction::South;
        assert_eq!(result.i, 51);
        assert_eq!(result.j, 75);
    }

    #[test]
    fn test_add_direction_unsigned_types() {
        let coord_usize = Coordinate::new(10usize, 20usize);
        let result = coord_usize + Direction::South;
        assert_eq!(result.i, 11);
        assert_eq!(result.j, 20);

        let coord_u32 = Coordinate::new(100u32, 200u32);
        let result = coord_u32 + Direction::East;
        assert_eq!(result.i, 100);
        assert_eq!(result.j, 201);

        let coord_u8 = Coordinate::new(10u8, 20u8);
        let result = coord_u8 + Direction::West;
        assert_eq!(result.i, 10);
        assert_eq!(result.j, 19);
    }

    #[test]
    fn test_add_assign_full_direction_signed_types() {
        let mut coord_i32 = Coordinate::new(10i32, 20i32);
        coord_i32 += direction::FullDirection::NorthEast;
        assert_eq!(coord_i32.i, 9);
        assert_eq!(coord_i32.j, 21);

        let mut coord_i64 = Coordinate::new(100i64, 200i64);
        coord_i64 += direction::FullDirection::SouthWest;
        assert_eq!(coord_i64.i, 101);
        assert_eq!(coord_i64.j, 199);

        let mut coord_isize = Coordinate::new(50isize, 75isize);
        coord_isize += direction::FullDirection::NorthWest;
        assert_eq!(coord_isize.i, 49);
        assert_eq!(coord_isize.j, 74);
    }

    #[test]
    fn test_add_assign_full_direction_unsigned_types() {
        let mut coord_usize = Coordinate::new(10usize, 20usize);
        coord_usize += direction::FullDirection::SouthEast;
        assert_eq!(coord_usize.i, 11);
        assert_eq!(coord_usize.j, 21);

        let mut coord_u32 = Coordinate::new(100u32, 200u32);
        coord_u32 += direction::FullDirection::NorthEast;
        assert_eq!(coord_u32.i, 99);
        assert_eq!(coord_u32.j, 201);

        let mut coord_u64 = Coordinate::new(500u64, 750u64);
        coord_u64 += direction::FullDirection::SouthWest;
        assert_eq!(coord_u64.i, 501);
        assert_eq!(coord_u64.j, 749);
    }

    #[test]
    fn test_add_full_direction_signed_types() {
        let coord_i32 = Coordinate::new(10i32, 20i32);
        let result = coord_i32 + direction::FullDirection::NorthEast;
        assert_eq!(result.i, 9);
        assert_eq!(result.j, 21);

        let coord_i16 = Coordinate::new(50i16, 60i16);
        let result = coord_i16 + direction::FullDirection::SouthWest;
        assert_eq!(result.i, 51);
        assert_eq!(result.j, 59);
    }

    #[test]
    fn test_add_full_direction_unsigned_types() {
        let coord_usize = Coordinate::new(10usize, 20usize);
        let result = coord_usize + direction::FullDirection::SouthEast;
        assert_eq!(result.i, 11);
        assert_eq!(result.j, 21);

        let coord_u16 = Coordinate::new(50u16, 50u16);
        let result = coord_u16 + direction::FullDirection::NorthWest;
        assert_eq!(result.i, 49);
        assert_eq!(result.j, 49);
    }

    #[test]
    #[should_panic(expected = "Coordinate overflow")]
    fn test_unsigned_underflow_direction() {
        let coord = Coordinate::new(0usize, 5usize);
        let _ = coord + Direction::North;
    }

    #[test]
    #[should_panic(expected = "Coordinate overflow")]
    fn test_unsigned_underflow_full_direction() {
        let coord = Coordinate::new(0usize, 0usize);
        let _ = coord + direction::FullDirection::NorthWest;
    }
}
