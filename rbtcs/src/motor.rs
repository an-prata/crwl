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
    pub fn set(
        &mut self,
        speed: f32,
    ) -> Result<serial::Packet<MotorHeader, MotorData>, InvalidSpeedError> {
        if !speed.is_finite() {
            return Err(InvalidSpeedError);
        }

        self.speed = speed.clamp(Self::MIN_SPEED, Self::MAX_SPEED);
        Ok(self.gen_packet())
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
            MotorHeader {
                addr: self.addr,
                cmd: MotorCmd::SetState,
            },
            MotorData::State(self.state as u32),
        ))
    }

    /// Generates a serial packet that can be sent by a `serial::Client` to the
    /// motor.
    #[must_use]
    pub fn gen_packet(&self) -> serial::Packet<MotorHeader, MotorData> {
        serial::Packet::new(
            MotorHeader {
                addr: self.addr,
                cmd: MotorCmd::SetSpeed,
            },
            MotorData::Speed(self.speed),
        )
    }
}

/// A motor controller state.
#[repr(u32)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum State {
    Enabled = 1u32,
    Disabled = 2u32,
}

/// Represents a serial packet header intended for a motr controller.
#[derive(Clone, Copy)]
pub struct MotorHeader {
    pub(crate) addr: u8,
    pub(crate) cmd: MotorCmd,
}

impl serial::Header for MotorHeader {
    fn extract<T, U>(packet: &serial::Packet<T, U>) -> serial::ExtractionResult<Self>
    where
        T: serial::Header,
        U: serial::Data,
    {
        match packet.head.get() {
            (a, c) if c == MotorCmd::SetSpeed as u8 => Ok(Self {
                addr: a,
                cmd: MotorCmd::SetSpeed,
            }),

            (a, c) if c == MotorCmd::SetState as u8 => Ok(Self {
                addr: a,
                cmd: MotorCmd::SetState,
            }),

            _ => Err(serial::ExtractionError),
        }
    }

    fn get(&self) -> (u8, u8) {
        (self.addr, self.cmd as u8)
    }
}

/// Data being sent to a motor controller, differs based on the requirments of
/// the command being sent.
#[derive(Clone, Copy)]
pub enum MotorData {
    Speed(f32),
    State(u32),
}

impl serial::Data for MotorData {
    fn extract<T, U>(packet: &serial::Packet<T, U>) -> serial::ExtractionResult<MotorData>
    where
        T: serial::Header,
        U: serial::Data,
    {
        let head = MotorHeader::extract(packet)?;

        match head.cmd {
            MotorCmd::SetSpeed => Ok(Self::Speed(f32::from_bits(packet.data.get()))),
            MotorCmd::SetState => Ok(Self::State(packet.data.get())),
        }
    }

    fn get(&self) -> u32 {
        match self {
            Self::Speed(v) => v.to_bits(),
            Self::State(v) => *v,
        }
    }
}

/// Represents the command of a packet sent to the motor controller.
#[repr(u8)]
#[derive(Clone, Copy)]
pub enum MotorCmd {
    /// Set the speed on of the motor.
    SetSpeed = 1u8,

    /// Set the state of the motor.
    SetState = 2u8,
}

/// An invalid speed was given to the motor.
#[derive(Debug, Clone)]
pub struct InvalidSpeedError;

impl fmt::Display for InvalidSpeedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid speed, must be a real decimal")
    }
}

impl Error for InvalidSpeedError {}
