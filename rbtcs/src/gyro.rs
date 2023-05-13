// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use crate::{serial, util::angle::Angle};
use std::{error::Error, fmt::Display};

/// Responsible for constructing requests for data from a gyro over the serial
/// bus.
pub struct Controller {
    /// Address of the gyro in the serial bus.
    addr: u8,

    /// Yaw value from most recent update.
    yaw: Option<Angle>,

    /// Roll value from most recent update.
    roll: Option<Angle>,

    /// Pitch value from most recent update.
    pitch: Option<Angle>,

    /// Yaw per second from most recent update.
    yaw_per_sec: Option<Angle>,

    /// Roll per second from most recent update.
    roll_per_sec: Option<Angle>,

    /// Pitch per second from most recent update.
    pitch_per_sec: Option<Angle>,

    /// Value to be considered zero for yaw.
    yaw_zero: Option<Angle>,

    /// Value to be considered zero for roll.
    roll_zero: Option<Angle>,

    /// Value to be considered zero for pitch.
    pitch_zero: Option<Angle>,
}

impl Controller {
    /// Creates a new gyro controller for a gyro on the given serial address.
    #[must_use]
    pub fn new(addr: u8) -> Self {
        Self {
            addr,
            yaw: None,
            roll: None,
            pitch: None,
            yaw_per_sec: None,
            roll_per_sec: None,
            pitch_per_sec: None,
            yaw_zero: None,
            roll_zero: None,
            pitch_zero: None,
        }
    }

    /// Updates this struct's values given packets received from the gyro, this
    /// will update whatever values are contained withing the given slice to the
    /// data contained within the packet with relevant data at the greatest
    /// index for each value.
    pub fn update<T, U>(&mut self, packets: &[serial::Packet<T, U>]) -> &Self
    where
        T: serial::Header,
        U: serial::Data,
    {
        for p in packets {
            if let Ok(h) = <GyroHeader as serial::Header>::extract(p) {
                let data = <f32 as serial::Data>::extract(p).ok();

                if h.addr != self.addr || data.is_none() {
                    continue;
                }

                match h.cmd {
                    Request::Yaw => {
                        self.yaw = data.and_then(|a| Some(Angle::from_radians(a as f64)))
                    }
                    Request::Roll => {
                        self.roll = data.and_then(|a| Some(Angle::from_radians(a as f64)))
                    }
                    Request::Pitch => {
                        self.pitch = data.and_then(|a| Some(Angle::from_radians(a as f64)))
                    }
                    Request::YawPerSec => {
                        self.yaw_per_sec = data.and_then(|a| Some(Angle::from_radians(a as f64)))
                    }
                    Request::RollPerSec => {
                        self.roll_per_sec = data.and_then(|a| Some(Angle::from_radians(a as f64)))
                    }
                    Request::PitchPerSec => {
                        self.pitch_per_sec = data.and_then(|a| Some(Angle::from_radians(a as f64)))
                    }
                };
            }
        }

        self
    }

    /// Produce a packet for given request.
    #[inline]
    #[must_use]
    pub fn request(&self, req: Request) -> serial::Packet<GyroHeader, f32> {
        serial::Packet::new(
            GyroHeader {
                addr: self.addr,
                cmd: req,
            },
            0f32,
        )
    }

    /// produces a packet to request all fields of the `gyro::Controller`
    /// struct.
    #[inline]
    #[must_use]
    pub fn request_all(&self) -> [serial::Packet<GyroHeader, f32>; 6] {
        [
            self.request(Request::Yaw),
            self.request(Request::Roll),
            self.request(Request::Pitch),
            self.request(Request::YawPerSec),
            self.request(Request::RollPerSec),
            self.request(Request::PitchPerSec),
        ]
    }

    /// Sets the "zero" position of the gyro, all angle gotten after this will
    /// be relative to this zero point.
    pub fn zero(&mut self) {
        self.yaw_zero = self.yaw;
        self.roll_zero = self.roll;
        self.pitch_zero = self.pitch;
    }

    /// Gets the gyro's yaw relative to set zero.
    pub fn yaw(&self) -> Option<Angle> {
        match self.yaw {
            Some(a) => Some(a - self.yaw_zero.unwrap_or_default()),
            None => None,
        }
    }

    /// Gets the gyro's roll relative to set zero.
    pub fn roll(&self) -> Option<Angle> {
        match self.roll {
            Some(a) => Some(a - self.roll_zero.unwrap_or_default()),
            None => None,
        }
    }

    /// Gets the gyro's pitch relative to set zero.
    pub fn pitch(&self) -> Option<Angle> {
        match self.pitch {
            Some(a) => Some(a - self.pitch_zero.unwrap_or_default()),
            None => None,
        }
    }

    /// Gets the gyro's yaw change per second.
    pub fn yaw_per_sec(&self) -> Option<Angle> {
        self.yaw_per_sec
    }

    /// Gets the gyro's roll change per second.
    pub fn roll_per_sec(&self) -> Option<Angle> {
        self.roll_per_sec
    }

    /// Gets the gyro's pitch change per second.
    pub fn pitch_per_sec(&self) -> Option<Angle> {
        self.pitch_per_sec
    }
}

pub type RequestResult<T> = Result<T, RequestError>;

#[derive(Clone, Copy, Debug)]
pub struct RequestError;

impl Error for RequestError {}

impl Display for RequestError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "failed requesting or receiving a requested packet")
    }
}

/// Represents a request to the physical gyro, by its controller, for a specific
/// piece of information.
#[repr(u8)]
#[derive(Clone, Copy)]
pub enum Request {
    Yaw = 0b0000_0001u8,
    Roll = 0b0000_0010u8,
    Pitch = 0b0000_01000u8,
    YawPerSec = Self::Yaw as u8 | Self::PER_SEC,
    RollPerSec = Self::Roll as u8 | Self::PER_SEC,
    PitchPerSec = Self::Pitch as u8 | Self::PER_SEC,
}

impl Request {
    /// The bit that when on denotes a request for a value per second.
    const PER_SEC: u8 = 0b0001_0000u8;
}

/// Represents packet headers used by the gyro.
#[derive(Clone, Copy)]
pub struct GyroHeader {
    pub(crate) addr: u8,
    pub(crate) cmd: Request,
}

impl serial::Header for GyroHeader {
    fn extract<T, U>(packet: &serial::Packet<T, U>) -> serial::ExtractionResult<Self>
    where
        T: serial::Header,
        U: serial::Data,
    {
        match packet.head.get() {
            (a, c) if c == Request::Yaw as u8 => Ok(Self {
                addr: a,
                cmd: Request::Yaw,
            }),

            (a, c) if c == Request::Roll as u8 => Ok(Self {
                addr: a,
                cmd: Request::Roll,
            }),

            (a, c) if c == Request::Pitch as u8 => Ok(Self {
                addr: a,
                cmd: Request::Pitch,
            }),

            (a, c) if c == Request::YawPerSec as u8 => Ok(Self {
                addr: a,
                cmd: Request::YawPerSec,
            }),

            (a, c) if c == Request::RollPerSec as u8 => Ok(Self {
                addr: a,
                cmd: Request::RollPerSec,
            }),

            (a, c) if c == Request::PitchPerSec as u8 => Ok(Self {
                addr: a,
                cmd: Request::PitchPerSec,
            }),

            _ => Err(serial::ExtractionError),
        }
    }

    fn get(&self) -> (u8, u8) {
        (self.addr, self.cmd as u8)
    }
}
