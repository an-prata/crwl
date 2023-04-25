// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use crate::serial::{self, Header};
use core::fmt;
use std::error::Error;

/// A scruct for interfacing with an arduino motor controller.
#[derive(Debug)]
pub struct Controller {
    /// Address of motor on the serial bus.
    addr: u8,

    /// Set speed of the controller.
    speed: f32,

    /// State of the motor controller.
    state: State,
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
        Controller {
            addr,
            speed: 0f32,
            state: State::Disabled,
        }
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

    /// Gets the state of the motor controller.
    #[inline]
    #[must_use]
    pub fn state(&self) -> State {
        self.state
    }

    /// Set the state of the motor. Returns `None` if the given state is the
    /// same as current.
    #[must_use]
    pub fn set_state(&mut self, state: State) -> Option<serial::Packet<MotorHeader, MotorData>> {
        if self.state == state {
            return None;
        }

        self.state = state;

        Some(serial::Packet::new(
            MotorHeader::new(self.addr, MotorCmd::SetState),
            self.state.into(),
        ))
    }

    /// Generates a serial packet that can be sent by a `serial::Client` to the
    /// motor.
    #[must_use]
    pub fn gen_packet(&self) -> serial::Packet<MotorHeader, MotorData> {
        serial::Packet::<MotorHeader>::new(
            MotorHeader::new(self.addr, MotorCmd::SetSpeed),
            serial::Data::FloatingPoint(self.speed),
        )
    }
}

#[repr(u32)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum State {
    Enabled = 1u32,
    Disabled = 2u32,
}

#[derive(Clone, Copy)]
pub enum MotorData {
    Speed(f32),
    State(u32),
}

impl serial::Data for MotorData {
    fn extract<T>(packet: &serial::Packet<T, u32>) -> Self
    where
        T: Header,
    {
        let (_, cmd) = packet.head.get();

        match cmd {
            MotorCmd::SetSpeed => Self::Speed(f32::from_bits(cmd)),
            MotorCmd::SetState => Self::State(cmd),
        }
    }

    fn get(&self) -> u32 {
        todo!()
    }
}

impl Into<u32> for MotorData {
    fn into(self) -> u32 {
        match self {
            Self::Speed(v) => v.to_bits(),
            Self::State(v) => v,
        }
    }
}

#[derive(Header, Clone, Copy)]
pub struct MotorHeader {
    addr: u8,
    cmd: u8,
}

/// Represents the command of a packet sent to the motor controller.
#[repr(u8)]
pub enum MotorCmd {
    /// No command or invalid command.
    None = 0u8,

    /// Set the speed on of the motor.
    SetSpeed = 1u8,

    /// Set the state of the motor.
    SetState = 2u8,
}

#[derive(Debug, Clone)]
pub struct InvalidSpeedError;

impl fmt::Display for InvalidSpeedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid speed, must be a real decimal")
    }
}

impl Error for InvalidSpeedError {}
