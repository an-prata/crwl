// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

mod controller;

use gilrs::{Axis, Gilrs};
use mecanum::{DriveState, DriveVector};

/// Unwraps a gilrs `Option<&AxisData>` to an `f32` or default.
macro_rules! unwrap_axis {
    ($axis:expr) => {
        $axis.map(|a| a.value()).unwrap_or_default()
    };
}

fn main() {
    let mut gilrs = Gilrs::new().unwrap();
    let mut active_gamepad_id = None;

    let mut drive_vector: DriveVector;
    let mut drive_state: DriveState;

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

            (drive_vector, drive_state) = mecanum::calc_4_axes_drive(
                unwrap_axis!(active_gamepad.axis_data(Axis::LeftStickX)) as f64,
                unwrap_axis!(active_gamepad.axis_data(Axis::LeftStickY)) as f64,
                unwrap_axis!(active_gamepad.axis_data(Axis::RightStickX)) as f64,
                unwrap_axis!(active_gamepad.axis_data(Axis::RightZ)) as f64
                    - unwrap_axis!(active_gamepad.axis_data(Axis::LeftZ)) as f64,
            );

            // TODO: Set motors based on drive state.
        }
    }
}
