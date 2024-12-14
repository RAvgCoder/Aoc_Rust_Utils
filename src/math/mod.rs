/// A utility struct for mathematical operations.
pub struct Math;

impl Math {
    /// Computes the greatest common divisor (GCD) of two integers.
    ///
    /// # Arguments
    ///
    /// * `a` - An integer.
    /// * `b` - Another integer.
    ///
    /// # Returns
    ///
    /// The GCD of the two integers.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::math::Math;
    /// assert_eq!(Math::gcd(54, 24), 6);
    /// assert_eq!(Math::gcd(48, 18), 6);
    /// ```
    pub const fn gcd(a: i64, b: i64) -> i64 {
        if b == 0 {
            a
        } else {
            Math::gcd(b, a % b)
        }
    }

    /// Computes the least common multiple (LCM) of two integers.
    ///
    /// # Arguments
    ///
    /// * `a` - An integer.
    /// * `b` - Another integer.
    ///
    /// # Returns
    ///
    /// The LCM of the two integers.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::math::Math;
    /// assert_eq!(Math::lcm(54, 24), 216);
    /// assert_eq!(Math::lcm(4, 5), 20);
    /// assert_eq!(Math::lcm(21, 6), 42);
    /// ```
    pub const fn lcm(a: i64, b: i64) -> i64 {
        a * b / Math::gcd(a, b)
    }

    /// Computes the modulus of two integers, ensuring a positive result.
    ///
    /// # Arguments
    ///
    /// * `a` - The dividend.
    /// * `b` - The divisor.
    ///
    /// # Returns
    ///
    /// The positive modulus of `a` and `b`.
    ///
    /// # Examples
    ///
    /// ```
    /// use aoc_utils_rust::math::Math;
    /// assert_eq!(Math::mod_(10, 3), 1);
    /// assert_eq!(Math::mod_(-10, 3), 2);
    /// assert_eq!(Math::mod_(10, 5), 0);
    /// ```
    #[inline(always)]
    pub const fn mod_(a: i64, b: u64) -> i64 {
        (a % b as i64 + b as i64) % b as i64
    }
}
