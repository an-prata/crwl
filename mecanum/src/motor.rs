// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use crate::serial;
use core::fmt;
use serial::Header;
use std::error::Error;

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
pub struct Controller {
    /// Address of motor on the serial bus.
    addr: u8,

    /// Set speed of the controller.
    speed: f32,
}

impl Controller {
    /// Maximum speed the motor can be set to, finite numbers greator than this
    /// will be clamped within range.
    pub const MAX_SPEED: f32 = 1f32;

    /// Minimum speed the motor can be set to, finite numbers less than this
    /// will be clamped within range.
    pub const MIN_SPEED: f32 = -Self::MAX_SPEED;

    /// Creates a new motor controller instance given the clock, set, and get
    /// pins associated with it.
    #[must_use]
    pub fn new(addr: u8) -> Self {
        Controller { addr, speed: 0f32 }
    }

    /// Sets the desired motor speed. Returns an error if `speed` is infinite or
    /// `NaN` (as checked by `f32::is_finite()`).
    pub fn set(&mut self, speed: f32) -> Result<(), InvalidSpeedError> {
        if !speed.is_finite() {
            return Err(InvalidSpeedError);
        }

        self.speed = speed.clamp(Self::MIN_SPEED, Self::MAX_SPEED);
        Ok(())
    }

    /// Gets the motor controller's set speed.
    #[inline]
    #[must_use]
    pub fn speed(&self) -> f32 {
        self.speed
    }

    /// Generates a serial packet that can be sent by a `serial::Client` to the
    /// motor.
    #[must_use]
    pub fn gen_packet(&self) -> serial::Packet<McHeader> {
        serial::Packet::<McHeader>::new(
            McHeader::new(self.addr, McCmd::SetSpeed),
            serial::Data::FloatingPoint(self.speed),
        )
    }
}

#[derive(Header, Clone, Copy)]
pub struct McHeader {
    addr: u8,
    cmd: u8,
}

impl McHeader {
    #[must_use]
    fn new(addr: u8, cmd: McCmd) -> Self {
        Self {
            addr,
            cmd: cmd as u8,
        }
    }
}

#[repr(u8)]
pub enum McCmd {
    SetSpeed = 1u8,
}

#[derive(Debug, Clone)]
pub struct InvalidSpeedError;

impl fmt::Display for InvalidSpeedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid speed, must be a real decimal")
    }
}

impl Error for InvalidSpeedError {}
