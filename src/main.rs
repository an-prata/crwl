// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

mod log;
use gilrs::{Axis, Button, EventType, Gilrs};
use mecanum::{angle::Angle, gyro, headless::DriveMode, motor, serial, DriveState, DriveVector};
use std::error::Error;

const CLIENT_CLOCK_PIN: u16 = 0u16;
const CLIENT_DATA_PIN: u16 = 1u16;
const SERVER_CLOCK_PIN: u16 = 2u16;
const SERVER_DATA_PIN: u16 = 3u16;

const GYRO_ADDR: u8 = 4u8;

const FR_MOTOR_ADDR: u8 = 0u8;
const FL_MOTOR_ADDR: u8 = 1u8;
const BR_MOTOR_ADDR: u8 = 2u8;
const BL_MOTOR_ADDR: u8 = 3u8;

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    let mut logger = log::Logger::new("~/crwl.log")?;

    let mut gilrs = Gilrs::new()?;
    let mut gamepad_id = None;

    let mut serial_client = serial::Client::new(CLIENT_CLOCK_PIN, CLIENT_DATA_PIN)?;
    let mut serial_server = serial::Server::new(SERVER_CLOCK_PIN, SERVER_DATA_PIN)?;

    let mut gyro = gyro::Controller::new(GYRO_ADDR);

    let mut drive_mode = DriveMode::Relative;

    let mut fr = motor::Controller::new(FR_MOTOR_ADDR);
    let mut fl = motor::Controller::new(FL_MOTOR_ADDR);
    let mut br = motor::Controller::new(BR_MOTOR_ADDR);
    let mut bl = motor::Controller::new(BL_MOTOR_ADDR);

    // Main crwl loop.
    loop {
        while let Some(event) = gilrs.next_event() {
            gamepad_id = Some(event.id);

            let gamepad = gilrs.gamepad(event.id);

            if event.event
                == EventType::ButtonReleased(
                    Button::Start,
                    gamepad.button_code(Button::Start).unwrap(),
                )
            {
                // Zero the gyro on start button release.
                gyro.zero();
                logger.log(log::Line::Info(String::from("Zeroed gyro angles")))?;
            } else if event.event
                == EventType::ButtonPressed(
                    Button::LeftThumb,
                    gamepad.button_code(Button::LeftThumb).unwrap(),
                )
            {
                // Toggle drive mode on left stick.
                match drive_mode {
                    DriveMode::Relative => drive_mode = DriveMode::Headless,
                    DriveMode::Headless => drive_mode = DriveMode::Relative,
                }

                logger.log(log::Line::Info(format!(
                    "Set drive mode to {:?}",
                    drive_mode
                )))?;
            }
        }

        // Start updating recorded value while we do not need the serial client
        // and server.
        let gyro_future = gyro.update(&mut serial_client, &mut serial_server);

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

            gyro_future.await?;

            let drive_vec = DriveVector {
                angle: Angle::from_radians(f64::atan2(left_y as f64, left_x as f64)),
                magnitude: right_z as f64 - left_z as f64,
                rotation: right_x as f64,
            };

            let drive_state = DriveState::new(drive_vec);

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
