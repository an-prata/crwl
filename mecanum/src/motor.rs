// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use core::fmt;
use gpio::{
    sysfs::{SysFsGpioInput, SysFsGpioOutput},
    GpioIn, GpioOut, GpioValue,
};
use std::{error::Error, io, sync::RwLock};

/// Spawns a thread for sending the given motor controller instance's data to
/// the physical motor controller. Assumes the instance to be
/// `Arc<RwLock<MotorController>>` and will produce a clone of the `Arc`.
#[macro_export]
macro_rules! spawn_motor_thread {
    ($controller:expr) => {
        let controller_clone = $controller.clone();
        thread::spawn(move || loop {
            controller_clone.write().unwrap().send().unwrap();
        })
    };
}

/// A scruct for interfacing with an arduino motor controller.
#[derive(Debug)]
pub struct MotorController {
    /// Pin for receiving data from the controller.
    clock: SysFsGpioInput,

    /// Pin for sending data to the controller.
    set: SysFsGpioOutput,

    /// Set speed of the controller. Read-Write lock is used to allow this feild
    /// to be mutated without a mutable reference to self, as using GPIO pins
    /// requires mutability.
    speed: RwLock<f64>,
}

impl MotorController {
    /// Creates a new motor controller instance given the clock, set, and get
    /// pins associated with it.
    pub fn new(clock_pin: u16, set_pin: u16) -> io::Result<Self> {
        Ok(MotorController {
            clock: SysFsGpioInput::open(clock_pin)?,
            set: SysFsGpioOutput::open(set_pin)?,
            speed: RwLock::new(0f64),
        })
    }

    /// Sets the desired motor speed.
    pub fn set(&self, speed: f64) -> Result<(), InvalidSpeedError> {
        if speed.is_nan() || !speed.is_finite() {
            return Err(InvalidSpeedError);
        }

        let mut w = self.speed.write().unwrap();
        *w = speed.clamp(-1f64, 1f64);
        Ok(())
    }

    /// Gets the motor controller's set speed.
    pub fn speed(&self) -> f64 {
        *self.speed.read().unwrap()
    }

    /// Send this instances speed to the physical motor controller.
    pub fn send(&mut self) -> io::Result<()> {
        let r = self.speed.read().unwrap();
        let val = *r as i16;

        for i in 0..i16::BITS {
            // Get the current bit of the number.
            let bit = val >> i & 1 != 0;

            // Wait for the clock pin to go high.
            while self.clock.read_value()? != GpioValue::High {}

            // Set value of set pin to the number's bit.
            self.set.set_value(bit)?;
        }

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct InvalidSpeedError;

impl fmt::Display for InvalidSpeedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid speed, must be a real decimal")
    }
}

impl Error for InvalidSpeedError {}
