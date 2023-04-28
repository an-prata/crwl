// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use gilrs::Button;
use rbtcs::{
    bot::{self, BotResult},
    gyro,
    headless::DriveMode,
    led_lights, mecanum, motor,
};
use std::time;

pub struct Crwl {
    motors: [motor::Controller; 4],
    drive_mode: DriveMode,
    gyro: gyro::Controller,
    leds: led_lights::Controller,
}

impl Crwl {
    const FR_ADDR: u8 = 1u8;
    const FL_ADDR: u8 = 2u8;
    const BR_ADDR: u8 = 3u8;
    const BL_ADDR: u8 = 4u8;
    const GYRO_ADDR: u8 = 5u8;
    const LED_ADDR: u8 = 6u8;

    pub fn new() -> Self {
        Self {
            motors: [
                motor::Controller::new(Self::FR_ADDR),
                motor::Controller::new(Self::FL_ADDR),
                motor::Controller::new(Self::BL_ADDR),
                motor::Controller::new(Self::BR_ADDR),
            ],
            drive_mode: DriveMode::Relative,
            gyro: gyro::Controller::new(5u8),
            leds: led_lights::Controller::new(Self::LED_ADDR),
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

    fn run_base<T>(
        &mut self,
        state: bot::State,
        serial_tx: &mut rbtcs::serial::Client,
        serial_rx: &mut rbtcs::serial::Server<T>,
    ) -> bot::BotResult<()>
    where
        T: gpio::GpioIn,
    {
        // TODO: this bitch async
        self.gyro.update(serial_tx, serial_rx);

        match serial_tx.send(self.leds.set_color(match state {
            bot::State::Emergency(_) => led_lights::Color::from_rgb(1f32, 0f32, 0f32),
            _ => led_lights::Color::from_rgb(1f32, 1f32, 1f32),
        })) {
            Ok(_) => Ok(()),
            Err(_) => Err(bot::BotError::new(String::from(
                "serial send failed for LED color set",
            ))),
        }
    }

    fn run_enabled<T>(
        &mut self,
        time: std::time::Instant,
        gp_inputs: &mut gilrs::Gilrs,
        serial_tx: &mut rbtcs::serial::Client,
        serial_rx: &mut rbtcs::serial::Server<T>,
    ) -> bot::BotResult<bot::State>
    where
        T: gpio::GpioIn,
    {
        let mut gp: Option<gilrs::Gamepad> = None;

        while let Some(event) = gp_inputs.next_event() {
            gp = Some(gp_inputs.gamepad(event.id));

            match event.event {
                gilrs::EventType::ButtonReleased(Button::LeftThumb, _) => {
                    self.drive_mode = match self.drive_mode {
                        DriveMode::Headless => DriveMode::Relative,
                        DriveMode::Relative => DriveMode::Headless,
                    }
                }
                gilrs::EventType::ButtonReleased(Button::Start, _) => self.gyro.zero(),
                _ => (),
            }
        }

        let gp = match gp {
            Some(g) => g,
            None => return Ok(bot::State::Enabled(Some(time))),
        };

        match mecanum::DriveState::new(mecanum::DriveVector::from_4_axes(
            match gp.axis_data(gilrs::Axis::LeftStickX) {
                Some(a) => a.value() as f64,
                None => 0f64,
            },
            match gp.axis_data(gilrs::Axis::LeftStickY) {
                Some(a) => a.value() as f64,
                None => 0f64,
            },
            match gp.axis_data(gilrs::Axis::RightStickX) {
                Some(a) => a.value() as f64,
                None => 0f64,
            },
            match gp.axis_data(gilrs::Axis::RightZ) {
                Some(a) => a.value() as f64,
                None => 0f64,
            } - match gp.axis_data(gilrs::Axis::LeftZ) {
                Some(a) => a.value() as f64,
                None => 0f64,
            },
        ))
        .speeds
        .iter()
        .zip(self.motors)
        .map(|(s, mut m)| {
            serial_tx.send(
                m.set(*s as f32)
                    .expect("output from `DriveState::new()` should always be valid"),
            )
        })
        .collect::<Result<Vec<_>, _>>()
        {
            Ok(_) => Ok(bot::State::Enabled(Some(time))),
            Err(_) => Err(bot::BotError::new(String::from(
                "could not send motor speeds over serial",
            ))),
        }
    }

    fn run_idling<T>(
        &mut self,
        time: std::time::Instant,
        serial_tx: &mut rbtcs::serial::Client,
        serial_rx: &mut rbtcs::serial::Server<T>,
    ) -> bot::BotResult<bot::State>
    where
        T: gpio::GpioIn,
    {
        Ok(bot::State::Idling(Some(time::Instant::now())))
    }

    fn run_disabled<T>(
        &mut self,
        time: std::time::Instant,
        serial_tx: &mut rbtcs::serial::Client,
        serial_rx: &mut rbtcs::serial::Server<T>,
    ) -> bot::BotResult<bot::State>
    where
        T: gpio::GpioIn,
    {
        match mecanum::DriveState::from(mecanum::DriveVector::from_3_axes(0f64, 0f64, 0f64))
            .speeds
            .iter()
            .zip(self.motors)
            .map(|(s, mut m)| {
                serial_tx.send(
                    m.set(*s as f32)
                        .expect("speed of 0 should never be invalid"),
                )
            })
            .collect::<Result<Vec<_>, _>>()
        {
            Ok(_) => Ok(bot::State::Disabled(Some(time))),
            Err(_) => Err(bot::BotError::new(String::from(
                "could not disable motors over serial",
            ))),
        }
    }

    fn run_emergency(&mut self, time: std::time::Instant) -> bot::BotResult<bot::State> {
        Ok(bot::State::Emergency(Some(time)))
    }
}
