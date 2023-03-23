// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use std::f64;

const FR_ANG: f64 = -f64::consts::FRAC_PI_4;
const FL_ANG: f64 = f64::consts::FRAC_PI_4;
const BR_ANG: f64 = f64::consts::FRAC_PI_4;
const BL_ANG: f64 = -f64::consts::FRAC_PI_4;

pub enum WheelPos {
    /// Front Right
    FR,

    /// Front Left
    FL,

    /// Back Right
    BR,

    /// Back Left
    BL,
}

/// Represents a single frame of the drive train's state and holds data for all
/// four motors/wheels.
#[derive(Debug, PartialEq, Clone, Copy)]
pub struct DriveState {
    fr: f64,
    fl: f64,
    br: f64,
    bl: f64,
}

/// Represents the complete movement vector created by a `DriveState`.
#[derive(Debug, PartialEq, Clone, Copy)]
pub struct DriveVector {
    /// The angle of translation in radians.
    angle: f64,

    /// The speed of translation, between 1 and -1.
    magnitude: f64,

    /// The speed of rotation.
    rotation: f64,
}

#[derive(Debug, PartialEq, Clone, Copy, Default)]
pub struct WheelVector {
    angle: f64,
    magnitude: f64,
}

impl DriveState {
    /// Creates a drive state given the desired translation speeds along the x
    /// (side to side) and y (forward and back) axes along with a turn factor.
    ///
    /// All arguments should be between 1 and -1.
    ///
    /// # Arguments
    ///
    /// * `translation_x` - The desired speed along the x axis, between 1 and -1.
    /// * `translation_y` - The desired speed along the y axis, between 1 and -1.
    /// * `rotation` - Speed of rotation, between 1 and -1, positive is clockwise.
    pub fn new(translation_x: f64, translation_y: f64, rotation: f64) -> Self {
        let magnitude = f64::sqrt(f64::powi(translation_x, 2) + f64::powi(translation_y, 2));
        let angle = f64::atan2(translation_y, translation_x);

        let fr_speed = f64::sin(angle + FR_ANG) * magnitude - rotation;
        let fl_speed = f64::sin(angle + FL_ANG) * magnitude + rotation;
        let br_speed = f64::sin(angle + BR_ANG) * magnitude - rotation;
        let bl_speed = f64::sin(angle + BL_ANG) * magnitude + rotation;

        DriveState {
            fr: fr_speed,
            fl: fl_speed,
            br: br_speed,
            bl: bl_speed,
        }
    }

    /// Gets one of four `WheelVector`s given a `WheelPos`.
    pub fn wheel_vec(&self, pos: WheelPos) -> WheelVector {
        match pos {
            WheelPos::FR => WheelVector {
                angle: FR_ANG,
                magnitude: self.fr,
            },
            WheelPos::FL => WheelVector {
                angle: FL_ANG,
                magnitude: self.fl,
            },
            WheelPos::BR => WheelVector {
                angle: BR_ANG,
                magnitude: self.br,
            },
            WheelPos::BL => WheelVector {
                angle: BL_ANG,
                magnitude: self.br,
            },
        }
    }

    pub fn drive_vec(&self) -> DriveVector {
        let vecs: [WheelVector; 4] = [
            self.wheel_vec(WheelPos::FR),
            self.wheel_vec(WheelPos::FL),
            self.wheel_vec(WheelPos::BR),
            self.wheel_vec(WheelPos::BL),
        ];

        let translation_vec = vecs.iter().copied().sum::<WheelVector>() / vecs.len() as f64;

        let rot_fr = f64::sin(translation_vec.angle - FR_ANG) * translation_vec.magnitude - self.fr;
        let rot_fl = -1_f64
            * (f64::sin(translation_vec.angle - FL_ANG) * translation_vec.magnitude - self.fl);
        let rot_br = f64::sin(translation_vec.angle - BR_ANG) * translation_vec.magnitude - self.br;
        let rot_bl = -1_f64
            * (f64::sin(translation_vec.angle - BL_ANG) * translation_vec.magnitude - self.bl);

        DriveVector {
            angle: translation_vec.angle,
            magnitude: translation_vec.magnitude,
            rotation: f64::max(f64::max(rot_fr, rot_fl), f64::max(rot_br, rot_bl)),
        }
    }
}

impl WheelVector {
    /// Manipulates the vector so that it points to the same coordinate but has
    /// a positive magnitude.
    ///
    /// e.g. A vector with direction π/2 and magnitude -1 will become a vector
    /// with direction 3π/2 and magnitude 1.
    pub fn abs(&self) -> Self {
        let mut ret: Self = self.clone();

        if ret.magnitude >= 0_f64 {
            return ret;
        }

        ret.magnitude = f64::abs(ret.magnitude);
        ret.angle = (ret.angle + f64::consts::PI) % f64::consts::TAU;

        ret
    }
}

impl std::ops::Add<WheelVector> for WheelVector {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self {
            angle: self.angle + other.angle,
            magnitude: self.magnitude + other.magnitude,
        }
    }
}

impl std::ops::Sub<WheelVector> for WheelVector {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        Self {
            angle: self.angle - other.angle,
            magnitude: self.magnitude - other.magnitude,
        }
    }
}

impl std::ops::Mul<f64> for WheelVector {
    type Output = Self;

    fn mul(self, other: f64) -> Self {
        Self {
            angle: self.angle,
            magnitude: self.magnitude * other,
        }
    }
}

impl std::ops::Div<f64> for WheelVector {
    type Output = Self;

    fn div(self, other: f64) -> Self {
        Self {
            angle: self.angle,
            magnitude: self.magnitude / other,
        }
    }
}

impl std::iter::Sum<WheelVector> for WheelVector {
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        iter.fold(Self::default(), |a, b| a + b)
    }
}

#[cfg(test)]
mod tests {
    use crate::mecanum;

    const MAX_ERR: f64 = 0.000000001;

    #[test]
    fn constructor() {
        let mut x: f64 = 0_f64;

        while x <= 1_f64 {
            let state = mecanum::DriveState::new(0_f64, x, 0_f64);

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

    #[test]
    fn drive_vec() {
        let mut x: f64 = 0_f64;

        while x <= 1_f64 {
            let state = mecanum::DriveState::new(0_f64, 0_f64, x);
            let drive_vec = state.drive_vec();

            println!("{}", x);

            assert_eq!(drive_vec.magnitude, 0_f64);
            assert_eq!(drive_vec.angle, 0_f64);

            assert!((drive_vec.rotation - x) < MAX_ERR);

            x += 0.1;
        }
    }
}
