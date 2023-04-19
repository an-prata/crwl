// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use crate::serial::{self, Header};

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
    pub fn set_color(&mut self, color: Color) {
        self.color = Some(color);
    }

    /// Generates a `serial::Packet<LedHeader>` for sending using a
    /// `serial::Client`. This packet will instruct the LED light controller to
    /// match the state of `self`.
    #[must_use]
    pub fn gen_packet(&mut self) -> serial::Packet<LedHeader> {
        serial::Packet::new(
            LedHeader::new(self.addr, LedCommand::Set),
            serial::Data::UnsignedInteger(match self.color {
                Some(mut c) => c.gen_u32(),
                None => Color::from_rgb(0f32, 0f32, 0f32).gen_u32(),
            }),
        )
    }
}

/// Represents a color that can be converted to RGB or HSV.
#[derive(Debug, Default, Clone, Copy)]
pub struct Color {
    rgb: Option<(f32, f32, f32)>,
    hsv: Option<(f32, f32, f32)>,
}

impl Color {
    /// Creates a new color given red, green, and blue values. All values will
    /// be clamped between 0 and 1.
    #[inline]
    #[must_use]
    pub fn from_rgb(r: f32, g: f32, b: f32) -> Self {
        Self {
            rgb: Some((
                r.clamp(0f32, 1f32),
                g.clamp(0f32, 1f32),
                b.clamp(0f32, 1f32),
            )),
            hsv: None,
        }
    }

    /// Creates a new clor given hue, saturation, and value values. All values
    /// will be clamped between 0 and 1 except for hue, which is between 0 and
    /// 360, clamped by `h.abs() % 360`.
    #[inline]
    #[must_use]
    pub fn from_hsv(h: f32, s: f32, v: f32) -> Self {
        Self {
            rgb: None,
            hsv: Some((h.abs() % 360f32, s.clamp(0f32, 1f32), v.clamp(0f32, 1f32))),
        }
    }

    /// Gets the RGB representation of this color.
    #[inline]
    #[must_use]
    pub fn rgb(&mut self) -> (f32, f32, f32) {
        match self.rgb {
            Some(rgb) => rgb,
            None => match self.hsv {
                Some(hsv) => self.gen_rgb(hsv),
                None => panic!("`Color` had no values"),
            },
        }
    }

    /// Gets the HSV representation of this color. Hue values are in degrees and
    /// between 0 and 360.
    #[inline]
    #[must_use]
    pub fn hsv(&mut self) -> (f32, f32, f32) {
        match self.hsv {
            Some(hsv) => hsv,
            None => match self.rgb {
                Some(rgb) => self.gen_hsv(rgb),
                None => panic!("`Color` had no values"),
            },
        }
    }

    /// Gets a `u32` in which the right most 8 bits are the B value or RGB,
    /// between 0 and 255, the next 8 bits to the left would be the G value, and
    /// the R value is the left 8 bits.
    #[must_use]
    pub fn gen_u32(&mut self) -> u32 {
        let (r, g, b) = self.rgb();

        0u32 | ((r * 255f32) as u32) << 2u32 * u8::BITS
            | ((g * 255f32) as u32) << u8::BITS
            | (b * 255f32) as u32
    }

    /// Calculates an RGB color truple given an HSV color tuple and caches it in
    /// `self`.
    #[must_use]
    fn gen_rgb(&mut self, hsv: (f32, f32, f32)) -> (f32, f32, f32) {
        let (mut h, s, v) = hsv;

        if s == 0f32 {
            return (v, v, v);
        }

        h /= 60f32;

        let i = h.trunc() as u16;
        let f = h - i as f32;

        let p = v * (1f32 - s);
        let q = v * (1f32 - s * f);
        let t = v * (1f32 - s * (1f32 - f));

        let rgb = match i {
            0 => (v, t, p),
            1 => (q, v, p),
            2 => (p, v, t),
            3 => (p, q, v),
            4 => (t, p, v),
            _ => (v, p, q),
        };

        self.rgb = Some(rgb);
        rgb
    }

    /// Calculates an HSV color truple given an rgb color tuple and caches it in
    /// `self`.
    #[must_use]
    fn gen_hsv(&mut self, rgb: (f32, f32, f32)) -> (f32, f32, f32) {
        let (r, g, b) = rgb;

        let max = r.max(g).max(b);
        let min = r.min(g).min(b);

        if max == 0f32 {
            return (0f32, 0f32, 0f32);
        }

        let s = 360f32 * (max - min) / max;

        if s == 0f32 {
            return (0f32, 0f32, max);
        }

        let h = {
            if max == r {
                (0f32 * 360f32 / 3f32) + (360f32 / 6f32) * (g - b) / (max - min)
            } else if max == g {
                (1f32 * 360f32 / 3f32) + (360f32 / 6f32) * (b - r) / (max - min)
            } else {
                (2f32 * 360f32 / 3f32) + (360f32 / 6f32) * (r - g) / (max - min)
            }
        };

        self.hsv = Some((h, s, max));
        (h, s, max)
    }
}

/// Header for LED light serial packets.
#[derive(Header, Clone, Copy)]
pub struct LedHeader {
    pub addr: u8,
    pub cmd: u8,
}

impl LedHeader {
    /// Creates a new `LedHeader`.
    #[inline]
    #[must_use]
    pub fn new(addr: u8, cmd: LedCommand) -> Self {
        Self {
            addr,
            cmd: cmd as u8,
        }
    }
}

/// A command for an LED controller.
#[repr(u8)]
pub enum LedCommand {
    Set = 1u8,
}
