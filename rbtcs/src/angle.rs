// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use aprox_eq::AproxEq;
use std::{
    f64,
    fmt::{self, Display, Formatter},
    ops::{Add, Div, Mul, Sub},
};

/// Represents an angle that can be converted or interperented in multiple
/// measurements. Angles do not preserve the number of turns, meaning that a
/// 365 degree angle will be turned into a 5 degree angle. The `Angle` struct
/// will however preserve direction, -90 degrees and 90 degrees are considered
/// distinct. The struct also guarantees that all measurements retrieved from it
/// will be less that one full rotation.
#[derive(AproxEq, Clone, Debug, Copy, PartialEq, Default)]
pub struct Angle {
    /// The fraction of a circle that this angle represents, all other
    /// measurements are derrived by converting this value, which is kept
    /// between -1 and 1 to reduce floating point error.
    pub fraction: f64,
}

impl Angle {
    /// Creates a new angle given radians.
    pub fn from_radians(radians: f64) -> Self {
        Angle {
            fraction: (radians / f64::consts::TAU) % 1f64,
        }
    }

    /// Creates a new angle given degrees.
    pub fn from_degrees(degrees: f64) -> Self {
        Angle {
            fraction: (degrees / 360_f64) % 1f64,
        }
    }

    /// Creates a new angle given a point. The angle that will be produced is
    /// the angle
    pub fn from_point(x: f64, y: f64) -> Self {
        Angle {
            fraction: (f64::atan2(y, x) / f64::consts::TAU) % 1f64,
        }
    }

    /// Gets the radian representation of the angle.
    pub fn radians(&self) -> f64 {
        self.fraction * f64::consts::TAU
    }

    /// Gets the degree representation of the angle.
    pub fn degrees(&self) -> f64 {
        self.fraction * 360f64
    }
}

impl Add<Angle> for Angle {
    type Output = Self;

    fn add(self, other: Angle) -> Self {
        Angle {
            fraction: (self.fraction + other.fraction) % 1f64,
        }
    }
}

impl Sub<Angle> for Angle {
    type Output = Self;

    fn sub(self, other: Angle) -> Self {
        Angle {
            fraction: (self.fraction - other.fraction) % 1f64,
        }
    }
}

impl Mul<f64> for Angle {
    type Output = Self;

    fn mul(self, other: f64) -> Self {
        Angle {
            fraction: (self.fraction * other) % 1f64,
        }
    }
}

impl Div<f64> for Angle {
    type Output = Self;

    fn div(self, other: f64) -> Self {
        Angle {
            fraction: (self.fraction / other) % 1f64,
        }
    }
}

impl Display for Angle {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}° / {}π / {}τ",
            self.degrees(),
            self.fraction * 2f64,
            self.fraction
        )
    }
}

#[cfg(test)]
mod tests {
    use super::Angle;
    use aprox_eq::{assert_aprox_eq, assert_aprox_ne};
    use std::f64;

    #[test]
    pub fn conversions() {
        let vals = [
            (0f64, 0f64, 0f64),
            (90f64, f64::consts::PI / 2f64, 0.25f64),
            (180f64, f64::consts::PI, 0.5f64),
            (270f64, f64::consts::PI * 1.5f64, 0.75f64),
        ];

        for (deg, rad, dec) in vals {
            let ang_deg = Angle::from_degrees(deg);
            let ang_rad = Angle::from_radians(rad);
            let ang_dec = Angle { fraction: dec };

            assert_aprox_eq!(ang_deg, ang_rad);
            assert_aprox_eq!(ang_rad, ang_dec);
            assert_aprox_eq!(ang_dec, ang_deg);
        }
    }

    #[test]
    pub fn single_rotation() {
        let angles = [
            Angle::from_radians(f64::consts::PI * 3f64),
            Angle::from_degrees(361f64),
            Angle::from_point(1f64, 2f64),
            Angle::from_point(0f64, 0f64),
            Angle::from_radians(f64::consts::TAU + 1f64.powi(-10)),
        ];

        for a in angles {
            assert!(a.fraction < 1f64);
        }
    }
}
