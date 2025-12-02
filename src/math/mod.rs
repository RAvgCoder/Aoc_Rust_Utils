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

    /// Computes the modular inverse of `a` modulo `m`.
    ///
    /// The modular inverse is an integer `x` such that:
    /// `a * x ≡ 1 (mod m)`
    ///
    /// # Arguments
    /// - `a`: The number for which the modular inverse is to be calculated.
    /// - `m`: The modulus.
    ///
    /// # Returns
    /// - `Some(inverse)` if the modular inverse exists (i.e., `a` and `m` are coprime).
    /// - `None` if the modular inverse does not exist.
    ///
    /// # Examples
    /// ```
    /// use aoc_utils_rust::math::Math;
    /// assert_eq!(Math::modular_inverse(3, 7), Some(5)); // 3 * 5 ≡ 1 (mod 7)
    /// assert_eq!(Math::modular_inverse(10, 17), Some(12)); // 10 * 12 ≡ 1 (mod 17)
    /// assert_eq!(Math::modular_inverse(6, 9), None); // No inverse as GCD(6, 9) != 1
    /// ```
    pub fn modular_inverse(a: i64, m: i64) -> Option<i64> {
        let (mut t, mut new_t) = (0, 1); // Coefficients for Bezout's identity
        let (mut r, mut new_r) = (m, a); // Remainders in the Euclidean algorithm

        // Extended Euclidean Algorithm
        while new_r != 0 {
            let quotient = r / new_r;

            // Update coefficients
            let temp_t = t - quotient * new_t;
            t = new_t;
            new_t = temp_t;

            // Update remainders
            let temp_r = r - quotient * new_r;
            r = new_r;
            new_r = temp_r;
        }

        // If the GCD is not 1, no modular inverse exists
        if r > 1 {
            return None;
        }

        // Ensure the modular inverse is positive
        if t < 0 {
            t += m;
        }

        Some(t)
    }
}
