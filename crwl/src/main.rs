// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

mod log;
use gilrs::{Axis, Gilrs};
use mecanum::{motor, serial};

const CLIENT_CLOCK_PIN: u16 = 0u16;
const CLIENT_DATA_PIN: u16 = 1u16;
const SERVER_CLOCK_PIN: u16 = 2u16;
const SERVER_DATA_PIN: u16 = 3u16;

const FR_MOTOR_ADDR: u8 = 0u8;
const FL_MOTOR_ADDR: u8 = 1u8;
const BR_MOTOR_ADDR: u8 = 2u8;
const BL_MOTOR_ADDR: u8 = 3u8;

/// Unwraps a gilrs `Option<&AxisData>` to an `f32` or default.
macro_rules! unwrap_axis {
    ($axis:expr) => {
        $axis.map(|a| a.value()).unwrap_or_default()
    };
}

fn main() {
    let mut logger = log::Logger::new("~/crwl.log").unwrap();

    let mut gilrs = Gilrs::new().unwrap();
    let mut active_gamepad_id = None;

    let serial_client = serial::Client::new(CLIENT_CLOCK_PIN, CLIENT_DATA_PIN);
    let serial_server = serial::Server::new(SERVER_CLOCK_PIN, SERVER_DATA_PIN);

    let mut fr = motor::Controller::new(FR_MOTOR_ADDR);
    let mut fl = motor::Controller::new(FL_MOTOR_ADDR);
    let mut br = motor::Controller::new(BR_MOTOR_ADDR);
    let mut bl = motor::Controller::new(BL_MOTOR_ADDR);

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

            let (_, drive_state) = mecanum::calc_4_axes_drive(
                unwrap_axis!(active_gamepad.axis_data(Axis::LeftStickX)) as f64,
                unwrap_axis!(active_gamepad.axis_data(Axis::LeftStickY)) as f64,
                unwrap_axis!(active_gamepad.axis_data(Axis::RightStickX)) as f64,
                unwrap_axis!(active_gamepad.axis_data(Axis::RightZ)) as f64
                    - unwrap_axis!(active_gamepad.axis_data(Axis::LeftZ)) as f64,
            );

            ok_or_log!(logger, fr.set(drive_state.fr as f32));
            ok_or_log!(logger, fl.set(drive_state.fl as f32));
            ok_or_log!(logger, br.set(drive_state.br as f32));
            ok_or_log!(logger, bl.set(drive_state.bl as f32));

            // TODO: Set motors based on drive state.
        }
    }
}
