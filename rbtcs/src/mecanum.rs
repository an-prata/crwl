// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use crate::util::angle::Angle;
use aprox_eq::AproxEq;
use std::f64;

/// The angle at which the front right wheel moves.
const FR_ANG: Angle = Angle {
    fraction: -f64::consts::FRAC_PI_4 / f64::consts::TAU,
};

/// The angle at which the front left wheel moves.
const FL_ANG: Angle = Angle {
    fraction: f64::consts::FRAC_PI_4 / f64::consts::TAU,
};

/// The angle at which the back right wheel moves.
const BR_ANG: Angle = Angle {
    fraction: f64::consts::FRAC_PI_4 / f64::consts::TAU,
};

/// The angle at which the back left wheel moves.
const BL_ANG: Angle = Angle {
    fraction: -f64::consts::FRAC_PI_4 / f64::consts::TAU,
};

/// Represents a complete movement in translation and rotation.
#[derive(AproxEq, Clone, Copy, Debug, Default, PartialEq)]
pub struct DriveVector {
    /// The angle of translation in radians.
    pub angle: Angle,

    /// The speed of translation, between 1 and -1.
    pub magnitude: f64,

    /// The speed of rotation.
    pub rotation: f64,
}

impl DriveVector {
    /// Creates a new `DriveVector` from the given translation speeds and
    /// rotation, all values should be between -1 and 1.
    ///
    /// # Arguments
    ///
    /// * `translation_x` - The translation speed along the x axis.
    /// * `translation_y` - The translation speed along the y axis.
    /// * `rotation` - Speed of rotation, positive is clockwise.
    #[inline]
    #[must_use]
    pub fn from_3_axes(translation_x: f64, translation_y: f64, rotation: f64) -> Self {
        DriveVector {
            angle: Angle::from_point(translation_x, translation_y),
            magnitude: f64::sqrt(f64::powi(translation_x, 2) + f64::powi(translation_y, 2)),
            rotation,
        }
    }

    /// Creates a new `DriveVector` from the given point, rotation speed, and
    /// translation speed.
    ///
    /// # Arguments
    ///
    /// * `x` - The x coordinate to "aim" for.
    /// * `y` - The y coordinate to "aim" for.
    /// * `rotation` - Speed of rotation, positive is clockwise.
    /// * `speed` - Translation speed, does not affect rotation.
    #[inline]
    #[must_use]
    pub fn from_4_axes(x: f64, y: f64, rotation: f64, speed: f64) -> Self {
        DriveVector {
            angle: Angle::from_point(x, y),
            magnitude: speed,
            rotation,
        }
    }
}

/// Represents a single frame of the drive train's state and holds data for all
/// four motors/wheels.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct DriveSpeeds {
    /// Motor speeds arranged going counter clockwise starting at the front
    /// right motor: fr, fl, bl, br.
    pub speeds: [f64; 4],
}

impl DriveSpeeds {
    /// Creates a `DriveSpeed` to achieve the given `DriveVector`.
    #[must_use]
    pub fn new(vec: DriveVector) -> Self {
        Self {
            speeds: [
                f64::sin((vec.angle + FR_ANG).radians()) * vec.magnitude - vec.rotation,
                f64::sin((vec.angle + FL_ANG).radians()) * vec.magnitude + vec.rotation,
                f64::sin((vec.angle + BL_ANG).radians()) * vec.magnitude + vec.rotation,
                f64::sin((vec.angle + BR_ANG).radians()) * vec.magnitude - vec.rotation,
            ]
            .map(|x| x.clamp(-1f64, 1f64)),
        }
    }
}

impl AproxEq for DriveSpeeds {
    fn aprox_eq(&self, other: &Self) -> bool {
        self.speeds
            .iter()
            .zip(other.speeds.iter())
            .any(|(a, b)| a == b)
    }
}

impl From<DriveVector> for DriveSpeeds {
    fn from(value: DriveVector) -> Self {
        Self::new(value)
    }
}

/// Creates a new `DriveVector` from the given translation speeds and
/// rotation, all values should be between -1 and 1. From that `DriveVector` a
/// `DriveSpeeds` is then created to achieve it.
///
/// # Arguments
///
/// * `translation_x` - The translation speed along the x axis.
/// * `translation_y` - The translation speed along the y axis.
/// * `rotation` - Speed of rotation, positive is clockwise.
#[inline]
#[must_use]
pub fn calc_3_axis_drive(
    translation_x: f64,
    translation_y: f64,
    rotation: f64,
) -> (DriveVector, DriveSpeeds) {
    let vec = DriveVector::from_3_axes(translation_x, translation_y, rotation);
    (vec, DriveSpeeds::new(vec))
}

/// Creates a new `DriveVector` from the given point, rotation speed, and
/// translation speed. From that `DriveVector` a `DriveSpeeds` is then created
/// to achieve it.
///
/// # Arguments
///
/// * `x` - The x coordinate to "aim" for.
/// * `y` - The y coordinate to "aim" for.
/// * `rotation` - Speed of rotation, positive is clockwise.
/// * `speed` - Translation speed, does not affect rotation.
#[inline]
#[must_use]
pub fn calc_4_axis_drive(x: f64, y: f64, rotation: f64, speed: f64) -> (DriveVector, DriveSpeeds) {
    let vec = DriveVector::from_4_axes(x, y, rotation, speed);
    (vec, DriveSpeeds::new(vec))
}

#[cfg(test)]
mod tests {
    use super::{DriveSpeeds, DriveVector};
    use aprox_eq::assert_aprox_eq;

    #[test]
    fn constructor() {
        let mut x: f64 = 0f64;

        while x <= 1f64 {
            let (vec3, state3) = super::calc_3_axis_drive(0f64, x, 0f64);
            let (vec4, state4) = super::calc_4_axis_drive(0f64, x, 0f64, x);

            assert_aprox_eq!(state3.speeds[0], state3.speeds[1]);
            assert_aprox_eq!(state3.speeds[3], state3.speeds[2]);
            assert_aprox_eq!(state3.speeds[0], state3.speeds[3]);

            assert_aprox_eq!(state3, state4);
            assert_aprox_eq!(vec3, vec4);

            x += 0.1;
        }
    }

    #[test]
    fn never_exceeds_one() {
        let mut x = -1f64;

        while x <= 1f64 {
            let mut y = -1f64;

            while y <= 1f64 {
                let mut s = -1f64;

                while s <= 1f64 {
                    let mut r = -1f64;

                    while r <= 1f64 {
                        let vec = DriveVector::from_4_axes(x, y, r, s);
                        let state = DriveSpeeds::new(vec);

                        assert!(state.speeds.iter().any(|x| x.abs() <= 1f64));

                        r += 0.05f64;
                    }

                    s += 0.05f64
                }

                y += 0.05f64
            }

            x += 0.05f64
        }
    }
}
