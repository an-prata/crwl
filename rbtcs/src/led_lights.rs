// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use crate::serial;
use crate::util::color::{Color, RgbValue};

/// Represents an LED light controller on the serial bus.
pub struct Controller {
    addr: u8,
    color: Option<Color>,
}

impl Controller {
    /// Creates a new LED light controller instance given its address.
    #[inline]
    #[must_use]
    pub fn new(addr: u8) -> Self {
        Self { addr, color: None }
    }

    /// Sets the color of the LED lights.
    #[inline]
    #[must_use]
    pub fn set_color(&mut self, color: Color) -> serial::Packet<LedHeader, Color> {
        self.color = Some(color);
        self.gen_packet()
    }

    /// Generates a `serial::Packet<LedHeader>` for sending using a
    /// `serial::Client`. This packet will instruct the LED light controller to
    /// match the state of `self`.
    #[must_use]
    pub fn gen_packet(&mut self) -> serial::Packet<LedHeader, Color> {
        serial::Packet::new(
            LedHeader {
                addr: self.addr,
                cmd: LedCommand::Set,
            },
            match self.color {
                Some(v) => v,
                None => Color::Rgb(RgbValue::new(0f32, 0f32, 0f32)),
            },
        )
    }
}

/// Header for LED light serial packets.
#[derive(Clone, Copy)]
pub struct LedHeader {
    pub(crate) addr: u8,
    pub(crate) cmd: LedCommand,
}

impl serial::Header for LedHeader {
    fn extract<T, U>(packet: &serial::Packet<T, U>) -> serial::ExtractionResult<Self>
    where
        T: serial::Header,
        U: serial::Data,
    {
        match packet.head.get() {
            (a, c) if c == LedCommand::Set as u8 => Ok(Self {
                addr: a,
                cmd: LedCommand::Set,
            }),

            _ => Err(serial::ExtractionError),
        }
    }

    fn get(&self) -> (u8, u8) {
        (self.addr, self.cmd as u8)
    }
}

/// A command for an LED controller.
#[repr(u8)]
#[derive(Clone, Copy, Debug)]
pub enum LedCommand {
    Set = 1u8,
}
