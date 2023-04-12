// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use std::{
    sync::{Arc, RwLock},
    thread,
};

use gilrs::{Axis, Gilrs};
use mecanum::{motor::MotorController, spawn_motor_thread, DriveState, DriveVector};

const FR_CLOCK_PIN: u16 = 0;
const FR_SET_PIN: u16 = 0;
const FL_CLOCK_PIN: u16 = 0;
const FL_SET_PIN: u16 = 0;
const BR_CLOCK_PIN: u16 = 0;
const BR_SET_PIN: u16 = 0;
const BL_CLOCK_PIN: u16 = 0;
const BL_SET_PIN: u16 = 0;

/// Unwraps a gilrs `Option<&AxisData>` to an `f32` or default.
macro_rules! unwrap_axis {
    ($axis:expr) => {
        $axis.map(|a| a.value()).unwrap_or_default()
    };
}

fn main() {
    let mut gilrs = Gilrs::new().unwrap();
    let mut active_gamepad_id = None;

    // Front right motor controller.
    let fr = Arc::new(RwLock::new(
        MotorController::new(FR_CLOCK_PIN, FR_SET_PIN).unwrap(),
    ));

    // Front left motor controller.
    let fl = Arc::new(RwLock::new(
        MotorController::new(FL_CLOCK_PIN, FR_SET_PIN).unwrap(),
    ));

    // Back right motor controller.
    let br = Arc::new(RwLock::new(
        MotorController::new(BR_CLOCK_PIN, BR_SET_PIN).unwrap(),
    ));

    // Back left motor contreller.
    let bl = Arc::new(RwLock::new(
        MotorController::new(BL_CLOCK_PIN, BL_SET_PIN).unwrap(),
    ));

    // let mut drive_vector: DriveVector;
    let mut drive_state: DriveState;

    // Start threads for all motors.
    spawn_motor_thread!(fr);
    spawn_motor_thread!(fl);
    spawn_motor_thread!(br);
    spawn_motor_thread!(bl);

    // Main crwl loop.
    loop {
        while let Some(event) = gilrs.next_event() {
            active_gamepad_id = Some(event.id);
        }

        if let Some(id) = active_gamepad_id {
            let active_gamepad = gilrs.gamepad(id);

            // TODO: Change drive state calculation based on gyro if in headless
            // mode, consider creating a constructor that utilises angle instead
            // of axes.

            (_, drive_state) = mecanum::calc_4_axes_drive(
                unwrap_axis!(active_gamepad.axis_data(Axis::LeftStickX)) as f64,
                unwrap_axis!(active_gamepad.axis_data(Axis::LeftStickY)) as f64,
                unwrap_axis!(active_gamepad.axis_data(Axis::RightStickX)) as f64,
                unwrap_axis!(active_gamepad.axis_data(Axis::RightZ)) as f64
                    - unwrap_axis!(active_gamepad.axis_data(Axis::LeftZ)) as f64,
            );

            fr.read().unwrap().set(drive_state.fr).unwrap();
            fl.read().unwrap().set(drive_state.fl).unwrap();
            br.read().unwrap().set(drive_state.br).unwrap();
            bl.read().unwrap().set(drive_state.bl).unwrap();

            // TODO: Set motors based on drive state.
        }
    }
}
