// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use std::f64;

const FR_ANG: f64 = -f64::consts::FRAC_PI_4;
const FL_ANG: f64 = f64::consts::FRAC_PI_4;
const BR_ANG: f64 = f64::consts::FRAC_PI_4;
const BL_ANG: f64 = -f64::consts::FRAC_PI_4;

/// Represents a complete movement in translation and rotation.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct DriveVector {
    /// The angle of translation in radians.
    pub angle: f64,

    /// The speed of translation, between 1 and -1.
    pub magnitude: f64,

    /// The speed of rotation.
    pub rotation: f64,
}

/// Represents a single frame of the drive train's state and holds data for all
/// four motors/wheels.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct DriveState {
    fr: f64,
    fl: f64,
    br: f64,
    bl: f64,
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
    pub fn from_3_axes(translation_x: f64, translation_y: f64, rotation: f64) -> Self {
        DriveVector {
            angle: f64::atan2(translation_y, translation_x),
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
    pub fn from_4_axes(x: f64, y: f64, rotation: f64, speed: f64) -> Self {
        DriveVector {
            angle: f64::atan2(y, x),
            magnitude: speed,
            rotation,
        }
    }
}

impl DriveState {
    /// Creates a `DriveState` to achieve the given `DriveVector`.
    pub fn new(vec: DriveVector) -> Self {
        let fr_speed = f64::sin(vec.angle + FR_ANG) * vec.magnitude - vec.rotation;
        let fl_speed = f64::sin(vec.angle + FL_ANG) * vec.magnitude + vec.rotation;
        let br_speed = f64::sin(vec.angle + BR_ANG) * vec.magnitude - vec.rotation;
        let bl_speed = f64::sin(vec.angle + BL_ANG) * vec.magnitude + vec.rotation;

        DriveState {
            fr: fr_speed,
            fl: fl_speed,
            br: br_speed,
            bl: bl_speed,
        }
    }
}

/// Creates a new `DriveVector` from the given translation speeds and
/// rotation, all values should be between -1 and 1. From that `DriveVector` a
/// `DriveState` is then created to achieve it.
///
/// # Arguments
///
/// * `translation_x` - The translation speed along the x axis.
/// * `translation_y` - The translation speed along the y axis.
/// * `rotation` - Speed of rotation, positive is clockwise.
pub fn calc_3_axes_drive(
    translation_x: f64,
    translation_y: f64,
    rotation: f64,
) -> (DriveVector, DriveState) {
    let vec = DriveVector::from_3_axes(translation_x, translation_y, rotation);
    (vec, DriveState::new(vec))
}

/// Creates a new `DriveVector` from the given point, rotation speed, and
/// translation speed. From that `DriveVector` a `DriveState` is then created to
/// achieve it.
///
/// # Arguments
///
/// * `x` - The x coordinate to "aim" for.
/// * `y` - The y coordinate to "aim" for.
/// * `rotation` - Speed of rotation, positive is clockwise.
/// * `speed` - Translation speed, does not affect rotation.
pub fn calc_4_axes_drive(x: f64, y: f64, rotation: f64, speed: f64) -> (DriveVector, DriveState) {
    let vec = DriveVector::from_4_axes(x, y, rotation, speed);
    (vec, DriveState::new(vec))
}

#[cfg(test)]
mod tests {
    use crate::drive;

    const MAX_ERR: f64 = 0.000000001;

    #[test]
    fn constructor() {
        let mut x: f64 = 0_f64;

        while x <= 1_f64 {
            let vec = drive::DriveVector::from_3_axes(0_f64, x, 0_f64);
            let state = drive::DriveState::new(vec);

            assert!(f64::abs(state.fr - state.fl) < MAX_ERR);
            assert!(f64::abs(state.br - state.bl) < MAX_ERR);
            assert!(f64::abs(state.fr - state.br) < MAX_ERR);

            assert!(state.fr <= 1_f64);
            assert!(state.fl <= 1_f64);
            assert!(state.br <= 1_f64);
            assert!(state.bl <= 1_f64);

            x += 0.1;
        }
    }
}
