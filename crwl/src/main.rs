// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

mod log;
use std::error::Error;

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

fn main() -> Result<(), Box<dyn Error>> {
    let mut logger = log::Logger::new("~/crwl.log")?;

    let mut gilrs = Gilrs::new()?;
    let mut gamepad_id = None;

    let mut serial_client = serial::Client::new(CLIENT_CLOCK_PIN, CLIENT_DATA_PIN)?;
    let mut serial_server = serial::Server::new(SERVER_CLOCK_PIN, SERVER_DATA_PIN)?;

    let mut fr = motor::Controller::new(FR_MOTOR_ADDR);
    let mut fl = motor::Controller::new(FL_MOTOR_ADDR);
    let mut br = motor::Controller::new(BR_MOTOR_ADDR);
    let mut bl = motor::Controller::new(BL_MOTOR_ADDR);

    // Main crwl loop.
    loop {
        while let Some(event) = gilrs.next_event() {
            gamepad_id = Some(event.id);
        }

        if let Some(id) = gamepad_id {
            let gamepad = gilrs.gamepad(id);

            // TODO: Change drive state calculation based on gyro if in headless
            // mode, consider creating a constructor that utilises angle instead
            // of axes.

            let left_x = match gamepad.axis_data(Axis::LeftStickX) {
                Some(n) => n.value(),
                None => {
                    logger.log(log::Line::Err(String::from(
                        "could not retrieve `Axis::LeftStickX`",
                    )))?;
                    0f32
                }
            };

            let left_y = match gamepad.axis_data(Axis::LeftStickY) {
                Some(n) => n.value(),
                None => {
                    logger.log(log::Line::Err(String::from(
                        "could not retrieve `Axis::LeftStickY`",
                    )))?;
                    0f32
                }
            };

            let right_x = match gamepad.axis_data(Axis::RightStickX) {
                Some(n) => n.value(),
                None => {
                    logger.log(log::Line::Err(String::from(
                        "could not retrieve `Axis::RightStickX`",
                    )))?;
                    0f32
                }
            };

            let right_z = match gamepad.axis_data(Axis::RightZ) {
                Some(n) => n.value(),
                None => {
                    logger.log(log::Line::Err(String::from(
                        "could not retrieve `Axis::RightZ`",
                    )))?;
                    0f32
                }
            };

            let left_z = match gamepad.axis_data(Axis::LeftZ) {
                Some(n) => n.value(),
                None => {
                    logger.log(log::Line::Err(String::from(
                        "could not retrieve `Axis::LeftZ`",
                    )))?;
                    0f32
                }
            };

            let (_, drive_state) = mecanum::calc_4_axes_drive(
                left_x as f64,
                left_y as f64,
                right_x as f64,
                right_z as f64 - left_z as f64,
            );

            logger.log_if_err(fr.set(drive_state.fr as f32));
            logger.log_if_err(fl.set(drive_state.fl as f32));
            logger.log_if_err(br.set(drive_state.br as f32));
            logger.log_if_err(bl.set(drive_state.bl as f32));

            serial_client.send(fr.gen_packet())?;
            serial_client.send(fl.gen_packet())?;
            serial_client.send(br.gen_packet())?;
            serial_client.send(bl.gen_packet())?;
        }
    }
}
