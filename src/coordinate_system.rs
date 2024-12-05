use std::fmt;
use std::ops::{Add, AddAssign};
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
/// assert_eq!(coord.manhattan_distance(), 7);
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
pub struct Coordinate {
    pub i: i32,
    pub j: i32,
}

impl Coordinate {
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
    pub const fn new(x: i32, y: i32) -> Self {
        Self { i: x, j: y }
    }

    /// Calculates the Manhattan distance from the origin.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// let coord = Coordinate::new(3, 4);
    /// assert_eq!(coord.manhattan_distance(), 7);
    /// ```
    pub const fn manhattan_distance(&self) -> i32 {
        self.i.abs() + self.j.abs()
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
    pub const fn transpose(&self) -> Self {
        Self::new(self.j, self.i)
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

impl Add<direction::Direction> for Coordinate {
    type Output = Self;

    /// Adds a `Direction` to the `Coordinate`.
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
    fn add(self, direction: direction::Direction) -> Self::Output {
        let (dx, dy) = direction.offset();
        Self {
            i: self.i + dx,
            j: self.j + dy,
        }
    }
}

impl From<(i32, i32)> for Coordinate {
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
    fn from((i, j): (i32, i32)) -> Self {
        Self::new(i, j)
    }
}

impl Add<direction::FullDirection> for Coordinate {
    type Output = Self;

    /// Adds a `FullDirection` to the `Coordinate`.
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
    fn add(self, direction: direction::FullDirection) -> Self::Output {
        let (dx, dy) = direction.offset();
        Self {
            i: self.i + dx,
            j: self.j + dy,
        }
    }
}

impl fmt::Debug for Coordinate {
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

impl FromStr for Coordinate {
    type Err = String;

    /// Implements the `FromStr` trait for the `Coordinate` struct, allowing it to be created from a string representation.
    ///
    /// # Examples
    ///
    /// ```
    /// use self::aoc_utils_rust::coordinate_system::Coordinate;
    /// use std::str::FromStr;
    /// let coord = Coordinate::from_str("3,4").unwrap();
    /// assert_eq!(coord.i, 3);
    /// assert_eq!(coord.j, 4);
    /// ```
    fn from_str(line: &str) -> Result<Self, Self::Err> {
        match line.split_once(',') {
            None => Err(format!("Invalid coordinate {}. Format is 'x,y'", line)),
            Some((i, j)) => {
                let x = i.parse().map_err(|err: std::num::ParseIntError| {
                    format!("Cannot parse i axis: {}", err)
                })?;
                let y = j.parse().map_err(|err: std::num::ParseIntError| {
                    format!("Cannot parse j axis: {}", err)
                })?;
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
        pub const fn offset(&self) -> (i32, i32) {
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
        pub const fn offset(&self) -> (i32, i32) {
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
