// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use crate::{
    angle::Angle,
    mecanum::{DriveSpeeds, DriveVector},
};

/// Represents a drive mode, namely the drive's frame of reference for controls.
#[derive(Debug)]
pub enum DriveMode {
    Headless(Angle),
    Relative,
}

/// Creates a new `DriveVector` from the given translation speeds and rotation,
/// all values should be between -1 and 1. From that `DriveVector` a
/// `DriveState` is then created to achieve it. Uses the given gyro angle to
/// make the drive move relative to the driver.
///
/// # Arguments
///
/// * `translation_x` - The translation speed along the x axis.
/// * `translation_y` - The translation speed along the y axis.
/// * `rotation` - Speed of rotation, positive is clockwise.
/// * `gyro_angle` - Current angle of the robot.
pub fn calc_3_axis_headless(
    translation_x: f64,
    translation_y: f64,
    rotation: f64,
    gyro_angle: Angle,
) -> (DriveVector, DriveSpeeds) {
    let vec = DriveVector {
        angle: Angle::from_radians(f64::atan2(translation_y, translation_x)) - gyro_angle,
        magnitude: f64::sqrt(f64::powi(translation_x, 2) + f64::powi(translation_y, 2)),
        rotation,
    };

    (vec, DriveSpeeds::new(vec))
}

/// Creates a new `DriveVector` from the given point, rotation speed, and
/// translation speed. From that `DriveVector` a `DriveState` is then created to
/// achieve it. The given gyro angle is used to make the drive moce relative to
/// the driver.
///
/// # Arguments
///
/// * `x` - The x coordinate to "aim" for.
/// * `y` - The y coordinate to "aim" for.
/// * `rotation` - Speed of rotation, positive is clockwise.
/// * `speed` - Translation speed, does not affect rotation.
/// * `gyro_angle` - Current angle of the robot.
pub fn calc_4_axis_headless(
    x: f64,
    y: f64,
    rotation: f64,
    speed: f64,
    gyro_angle: Angle,
) -> (DriveVector, DriveSpeeds) {
    let vec = DriveVector {
        angle: Angle::from_radians(f64::atan2(y, x)) - gyro_angle,
        magnitude: speed,
        rotation,
    };

    (vec, DriveSpeeds::new(vec))
}
