// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use std::io;

use crate::{angle::Angle, serial};

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

    /// Updates all this structs values. This will block the current thread
    /// until completion.
    pub async fn update(
        &mut self,
        client: &mut serial::Client,
        serv: &mut serial::Server,
    ) -> io::Result<()> {
        self.yaw = Some(Angle::from_radians(
            self.request(client, serv, Request::Yaw).await? as f64,
        ));

        self.roll = Some(Angle::from_radians(
            self.request(client, serv, Request::Roll).await? as f64,
        ));

        self.pitch = Some(Angle::from_radians(
            self.request(client, serv, Request::Pitch).await? as f64,
        ));

        self.yaw_per_sec = Some(Angle::from_radians(
            self.request(client, serv, Request::YawPerSec).await? as f64,
        ));

        self.roll_per_sec = Some(Angle::from_radians(
            self.request(client, serv, Request::RollPerSec).await? as f64,
        ));

        self.pitch_per_sec = Some(Angle::from_radians(
            self.request(client, serv, Request::PitchPerSec).await? as f64,
        ));

        Ok(())
    }

    /// Manually requests a newly updated value from the gyro, this will block
    /// the current thread until the request in fulfilled, though it should be
    /// fairly quick.
    pub async fn request(
        &mut self,
        client: &mut serial::Client,
        serv: &mut serial::Server,
        req: Request,
    ) -> io::Result<f32> {
        let packet = serial::Packet::new(self.gen_header(req), 0u32);

        let head = match client.send(&packet) {
            Ok(h) => h,
            Err(e) => return Err(io::Error::new(io::ErrorKind::Other, e)),
        };

        Ok(serv.listen_for::<GyroHeader, f32>(head).await?)
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

    /// Generates a header for the given command and gyro.
    fn gen_header(&self, cmd: Request) -> GyroHeader {
        GyroHeader {
            addr: self.addr,
            cmd,
        }
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
struct GyroHeader {
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
