// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use crate::log;
use gilrs::{Button, GamepadId};
use rbtcs::{
    bot, gyro,
    headless::{self, DriveMode},
    led_lights, mecanum, motor, serial,
};
use std::time;

pub struct Crwl {
    motors: [motor::Controller; 4],
    drive_mode: DriveMode,
    gyro: gyro::Controller,
    leds: led_lights::Controller,
    log: log::Logger,
}

impl Crwl {
    /// Odered from the front right counter clockwise: fr, fl, bl, br.
    const MOTOR_ADDRS: [u8; 4] = [1u8, 2u8, 3u8, 4u8];

    const GYRO_ADDR: u8 = 5u8;
    const LED_ADDR: u8 = 6u8;

    const LOG_PATH: &str = "~/crwl.log";

    pub fn new() -> Self {
        Self {
            motors: Self::MOTOR_ADDRS.map(|a| motor::Controller::new(a)),
            drive_mode: DriveMode::Relative,
            gyro: gyro::Controller::new(Self::GYRO_ADDR),
            leds: led_lights::Controller::new(Self::LED_ADDR),
            log: log::Logger::new(Self::LOG_PATH).unwrap(),
        }
    }
}

impl bot::Bot for Crwl {
    const TX_CLOCK: u16 = 0u16;
    const TX_DATA: u16 = 1u16;
    const RX_CLOCK: u16 = 2u16;
    const RX_DATA: u16 = 3u16;
    const RELAY_PIN: u16 = 4u16;
    const SERIAL_CYCLE: time::Duration = time::Duration::from_millis(2u64);

    fn run_base(
        &mut self,
        state: bot::State,
        serial_tx: &mut rbtcs::serial::Client,
        serial_rx: &mut rbtcs::serial::Server,
    ) -> bot::BotResult<bot::State> {
        let headers: Vec<gyro::GyroHeader> = self
            .gyro
            .request_all()
            .iter()
            .map(|r| serial_tx.send(*r))
            .filter(|r| r.is_ok())
            .map(|r| r.unwrap())
            .collect();

        match serial_tx.send(self.leds.set_color(match state {
            bot::State::Emergency(_) => led_lights::Color::from_rgb(1f32, 0f32, 0f32),
            _ => led_lights::Color::from_rgb(1f32, 1f32, 1f32),
        })) {
            Ok(_) => Ok(()),
            Err(_) => Err(bot::BotError::new(String::from(
                "serial send failed for LED color set",
            ))),
        }?;

        self.gyro.update(
            headers
                .iter()
                .map(|h| serial_rx.get(*h))
                .filter(|r| r.is_some())
                .map(|r| r.unwrap())
                .collect::<Vec<serial::Packet<_, _>>>()
                .as_slice(),
        );

        Ok(state)
    }

    fn run_enabled(
        &mut self,
        time: std::time::Instant,
        gp_inputs: &mut gilrs::Gilrs,
        serial_tx: &mut rbtcs::serial::Client,
        _serial_rx: &mut rbtcs::serial::Server,
    ) -> bot::BotResult<bot::State> {
        let mut gp_id: Option<GamepadId> = None;

        while let Some(event) = gp_inputs.next_event() {
            gp_id = Some(event.id);

            match event.event {
                gilrs::EventType::ButtonReleased(Button::LeftThumb, _) => {
                    self.drive_mode = match self.drive_mode {
                        DriveMode::Headless(_) => {
                            self.log
                                .log(log::Line::Info(String::from("drive mode: relative")))
                                .unwrap();

                            DriveMode::Relative
                        }

                        DriveMode::Relative => match self.gyro.yaw() {
                            Some(v) => {
                                self.log
                                    .log(log::Line::Info(format!("drive mode: headless @ {}", v)))
                                    .unwrap();

                                DriveMode::Headless(v)
                            }
                            None => {
                                self.log
                                    .log(log::Line::Warn(String::from(
                                        "drive mode: attempted to set headless with angle `None`",
                                    )))
                                    .unwrap();

                                DriveMode::Relative
                            }
                        },
                    }
                }

                gilrs::EventType::ButtonReleased(Button::Start, _) => {
                    self.log
                        .log(log::Line::Info(String::from("gyro: zeroed angles")))
                        .unwrap();

                    self.gyro.zero()
                }

                _ => (),
            }
        }

        let gp = match gp_id {
            Some(id) => gp_inputs.gamepad(id),
            None => return Ok(bot::State::Enabled(Some(time))),
        };

        let left_x = match gp.axis_data(gilrs::Axis::LeftStickX) {
            Some(a) => a.value() as f64,
            None => 0f64,
        };

        let left_y = match gp.axis_data(gilrs::Axis::LeftStickY) {
            Some(a) => a.value() as f64,
            None => 0f64,
        };

        let right_x = match gp.axis_data(gilrs::Axis::RightStickX) {
            Some(a) => a.value() as f64,
            None => 0f64,
        };

        let speed = match gp.axis_data(gilrs::Axis::RightZ) {
            Some(a) => a.value() as f64,
            None => 0f64,
        } - match gp.axis_data(gilrs::Axis::LeftZ) {
            Some(a) => a.value() as f64,
            None => 0f64,
        };

        match match self.drive_mode {
            DriveMode::Relative => mecanum::calc_4_axis_drive(left_x, left_y, right_x, speed),
            DriveMode::Headless(v) => {
                headless::calc_4_axis_headless(left_x, left_y, right_x, speed, v)
            }
        }
        .1
        .speeds
        .iter()
        .zip(0..self.motors.len())
        .map(|(s, m)| {
            serial_tx.send(
                self.motors[m]
                    .set(*s as f32)
                    .expect("output from `DriveState::new()` should always be valid"),
            )
        })
        .collect::<Result<Vec<_>, _>>()
        {
            Ok(_) => Ok(bot::State::Enabled(Some(time))),
            Err(_) => {
                self.log
                    .log(log::Line::Err(String::from(
                        "serial: could not send motor speeds",
                    )))
                    .unwrap();

                Err(bot::BotError::new(String::from(
                    "could not send motor speeds over serial",
                )))
            }
        }
    }

    fn run_idling(
        &mut self,
        _time: std::time::Instant,
        _serial_tx: &mut rbtcs::serial::Client,
        _serial_rx: &mut rbtcs::serial::Server,
    ) -> bot::BotResult<bot::State> {
        Ok(bot::State::Idling(Some(time::Instant::now())))
    }

    fn run_disabled(
        &mut self,
        time: std::time::Instant,
        serial_tx: &mut rbtcs::serial::Client,
        _serial_rx: &mut rbtcs::serial::Server,
    ) -> bot::BotResult<bot::State> {
        match mecanum::DriveState::from(mecanum::DriveVector::from_3_axes(0f64, 0f64, 0f64))
            .speeds
            .iter()
            .zip(0..self.motors.len())
            .map(|(s, m)| {
                serial_tx.send(
                    self.motors[m]
                        .set(*s as f32)
                        .expect("speed of 0 should never be invalid"),
                )
            })
            .collect::<Result<Vec<_>, _>>()
        {
            Ok(_) => Ok(bot::State::Disabled(Some(time))),
            Err(_) => {
                self.log
                    .log(log::Line::Err(String::from(
                        "serial: could not send motor speeds",
                    )))
                    .unwrap();

                Err(bot::BotError::new(String::from(
                    "could not send motor speeds over serial",
                )))
            }
        }
    }

    fn run_emergency(&mut self, time: std::time::Instant) -> bot::BotResult<bot::State> {
        Ok(bot::State::Emergency(Some(time)))
    }
}
