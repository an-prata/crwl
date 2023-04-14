// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

// Makes it so the `aprox_eq::*` path works within this crate for tests.
extern crate self as aprox_eq;
pub use aprox_derive::AproxEq;

/// Trait for aproximate equality, mostly for dealing with small amounts of
/// error that accumulate in floating point numbers which can be particularly
/// annoying when trying to unit test.
///
/// ## Derivable
///
/// This trait can be derived, doing so implements `aprox_eq()` so that it
/// compares all fields of the two structs, if one field is not aproximately
/// equal then neither is the struct. This requires that all fields also
/// implement `AproxEq`. The default implementation of `aprox_ne()` is used
/// if `AproxEq` is derived.
pub trait AproxEq<T = Self>
where
    T: ?Sized,
{
    /// Should return true if the two operands are aproximately equal, the
    /// exact meaning of "aproximate" is up to the implementing struct to
    /// decide but should be narrow enough that no values with a practical
    /// difference are aproximately equal and vise versa.
    ///
    /// # Examples
    ///
    /// ```
    /// use crate::aprox_eq::AproxEq;
    ///
    /// let a = 0.2_f32;
    /// let b = 0.3_f32;
    ///
    /// (a).aprox_eq(&b);  // This should probably be false.
    ///
    /// let a = 0.8_f64;
    /// let b = 0.7999999999_f64;
    ///
    /// (a).aprox_eq(&b);  // This is definately almost same number.
    /// ```
    #[must_use]
    fn aprox_eq(&self, other: &T) -> bool;

    /// Returns true if not aproximately equal, simple negation of `aprox_eq()`
    /// by default.
    ///
    /// # Examples
    ///
    /// ```
    /// use crate::aprox_eq::AproxEq;
    ///
    /// let a = 1_f32;
    /// let b = 1_f32;
    /// let c = 2_f32;
    ///
    /// a.aprox_ne(&b);  // false
    /// a.aprox_ne(&c);  // true
    /// ```
    #[inline]
    #[must_use]
    fn aprox_ne(&self, other: &T) -> bool {
        !self.aprox_eq(other)
    }
}

/// Behaves exactly like `assert_eq!` but calls on the `aprox_eq()` function as
/// provided by the `AproxEq` trait instead of `eq()`.
#[macro_export]
macro_rules! assert_aprox_eq {
    ($left:expr, $right:expr) => {
        assert!(
            aprox_eq::AproxEq::aprox_eq(&$left, &$right),
            "assertion failed: `left.aprox_eq(right)`\n  left: `{:#?}`,\n right: `{:#?}`",
            $left,
            $right,
        );
    };
}

/// Behaves exactly like `assert_ne!` but calls on the `aprox_ne()` function as
/// provided by the `AproxEq` trait instead of `ne()`.
#[macro_export]
macro_rules! assert_aprox_ne {
    ($left:expr, $right:expr) => {
        assert!(
            aprox_eq::AproxEq::aprox_ne(&$left, &$right),
            "assertion failed: `left.aprox_ne(right)`\n  left: `{:#?}`,\n right: `{:#?}`",
            $left,
            $right,
        );
    };
}

impl AproxEq for f64 {
    fn aprox_eq(&self, other: &Self) -> bool {
        // Aproximately equal if within 10^-10 of eachother.
        (self - other).abs() < 1_f64.powi(-10)
    }
}

impl AproxEq for f32 {
    fn aprox_eq(&self, other: &Self) -> bool {
        // Aproximately equal if within 10^-8 of eachother.
        (self - other).abs() < 10_f32.powi(-8)
    }
}

#[cfg(test)]
mod tests {
    use crate::AproxEq;
    use aprox_derive::AproxEq;

    #[derive(AproxEq, Debug)]
    struct SomeFoats {
        pub a: f64,
        pub b: f32,
    }

    #[derive(AproxEq, Debug)]
    struct SomeAproxEq {
        pub a: SomeFoats,
        pub b: SomeFoats,
    }

    #[test]
    fn basic_aprox_eq() {
        assert_aprox_eq!(1.0002_f64, 1.000199999_f64);
        assert_aprox_ne!(1.002_f32, 1.001_f32);
    }

    #[test]
    fn ownership_retainance() {
        let a = 1_f64;
        let b = 1_f64;

        assert_aprox_eq!(a, b);

        let c = a + b;

        assert_aprox_ne!(a, c);
    }

    #[test]
    fn derive_test() {
        assert_aprox_eq!(
            SomeFoats { a: 3f64, b: 2f32 },
            SomeFoats { a: 3f64, b: 2f32 }
        );

        assert_aprox_eq!(
            SomeAproxEq {
                a: SomeFoats { a: 3f64, b: 2f32 },
                b: SomeFoats { a: 5f64, b: 4f32 }
            },
            SomeAproxEq {
                a: SomeFoats { a: 3f64, b: 2f32 },
                b: SomeFoats { a: 5f64, b: 4f32 }
            }
        );
    }
}
