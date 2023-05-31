// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use rbtcs::{gyro, headless, util::angle::Angle};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub struct State {
    drive_mode: headless::DriveMode,
    drive_motor_speeds: [f32; 4],
    gyro_yaw: Option<Angle>,
    gyro_roll: Option<Angle>,
    gyro_pitch: Option<Angle>,
    gyro_yaw_per_sec: Option<Angle>,
    gyro_roll_per_sec: Option<Angle>,
    gyro_pitch_per_sec: Option<Angle>,
}

impl State {
    pub fn new(
        drive_mode: headless::DriveMode,
        drive_motor_speeds: [f32; 4],
        gyro: &gyro::Controller,
    ) -> Self {
        Self {
            drive_mode,
            drive_motor_speeds,
            gyro_yaw: gyro.yaw(),
            gyro_roll: gyro.roll(),
            gyro_pitch: gyro.pitch(),
            gyro_yaw_per_sec: gyro.yaw_per_sec(),
            gyro_roll_per_sec: gyro.roll_per_sec(),
            gyro_pitch_per_sec: gyro.pitch_per_sec(),
        }
    }
}
