// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use aprox_eq::AproxEq;

use crate::serial;

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
                None => Color::from_rgb(0f32, 0f32, 0f32),
            },
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

    /// Creates a new `Color` from a `u32` in which the right most 8 bits are
    /// the blue value, the next 8 are the green value, and the next 8 are the
    /// red value.
    #[must_use]
    pub fn from_u32(n: u32) -> Self {
        let r = ((n >> (u8::BITS * 2)) as u8) as f32 / 255f32;
        let g = ((n >> u8::BITS) as u8) as f32 / 255f32;
        let b = (n as u8) as f32 / 255f32;

        Self::from_rgb(r, g, b)
    }

    /// Gets the RGB representation of this color.
    #[inline]
    #[must_use]
    pub fn rgb(&self) -> (f32, f32, f32) {
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
    pub fn hsv(&self) -> (f32, f32, f32) {
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
    pub fn gen_u32(&self) -> u32 {
        let (r, g, b) = self.rgb();

        0u32 | ((r * 255f32) as u32) << 2u32 * u8::BITS
            | ((g * 255f32) as u32) << u8::BITS
            | (b * 255f32) as u32
    }

    /// Calculates an RGB color truple given an HSV color tuple and caches it in
    /// `self`.
    #[must_use]
    fn gen_rgb(&self, hsv: (f32, f32, f32)) -> (f32, f32, f32) {
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

        rgb
    }

    /// Calculates an HSV color truple given an rgb color tuple and caches it in
    /// `self`.
    #[must_use]
    fn gen_hsv(&self, rgb: (f32, f32, f32)) -> (f32, f32, f32) {
        let (r, g, b) = rgb;

        let max = r.max(g).max(b);
        let min = r.min(g).min(b);

        if max == 0f32 {
            return (0f32, 0f32, 0f32);
        }

        let s = (max - min) / max;

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

        (h, s, max)
    }
}

impl serial::Data for Color {
    fn extract<T, U>(packet: &serial::Packet<T, U>) -> serial::ExtractionResult<Self>
    where
        T: serial::Header,
        U: serial::Data,
    {
        Ok(Self::from_u32(packet.data.get()))
    }

    fn get(&self) -> u32 {
        self.gen_u32()
    }
}

impl AproxEq for Color {
    fn aprox_eq(&self, other: &Self) -> bool {
        let (a, b) = (self.rgb(), other.rgb());
        a.0.aprox_eq(&b.0) && a.1.aprox_eq(&b.1) && a.2.aprox_eq(&b.2)
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

#[cfg(test)]
mod tests {
    use aprox_eq::assert_aprox_eq;

    use super::Color;

    #[test]
    pub fn hsv_to_rgb() {
        let color_pairs = [
            (
                Color::from_rgb(1f32, 0f32, 0f32),
                Color::from_hsv(0f32, 1f32, 1f32),
            ),
            (
                Color::from_rgb(0f32, 1f32, 0f32),
                Color::from_hsv(120f32, 1f32, 1f32),
            ),
            (
                Color::from_rgb(0f32, 0f32, 1f32),
                Color::from_hsv(240f32, 1f32, 1f32),
            ),
            (
                Color::from_rgb(0.5f32, 0.5f32, 0.5f32),
                Color::from_hsv(0f32, 0f32, 0.5f32),
            ),
        ];

        for (rgb, hsv) in color_pairs {
            assert_aprox_eq!(rgb, hsv);

            assert_aprox_eq!(rgb.rgb().0, hsv.rgb().0);
            assert_aprox_eq!(rgb.rgb().1, hsv.rgb().1);
            assert_aprox_eq!(rgb.rgb().2, hsv.rgb().2);

            assert_aprox_eq!(rgb.hsv().0, hsv.hsv().0);
            assert_aprox_eq!(rgb.hsv().1, hsv.hsv().1);
            assert_aprox_eq!(rgb.hsv().2, hsv.hsv().2);
        }
    }
}
