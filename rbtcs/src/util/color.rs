// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use crate::serial;
use aprox_eq::AproxEq;
use std::u8;

#[derive(Clone, Copy, Debug)]
pub enum Color {
    Rgb(RgbValue),
    Hsv(HsvValue),
}

impl serial::Data for Color {
    fn extract<U, V>(packet: &serial::Packet<U, V>) -> serial::ExtractionResult<Self>
    where
        U: serial::Header,
        V: serial::Data,
    {
        Ok(Self::Rgb(RgbValue::from(packet.data.get())))
    }

    fn get(&self) -> u32 {
        (*self).into()
    }
}

impl From<Color> for u32 {
    fn from(value: Color) -> Self {
        let rgb = match value {
            Color::Rgb(v) => v,
            Color::Hsv(v) => v.into(),
        };

        rgb.into()
    }
}

impl From<u32> for Color {
    fn from(value: u32) -> Self {
        value.into()
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct RgbValue(pub u8, pub u8, pub u8);

impl RgbValue {
    pub fn from_dec(r: f32, g: f32, b: f32) -> Self {
        Self((r * 255f32) as u8, (g * 255f32) as u8, (b * 255f32) as u8)
    }
}

impl From<HsvValue> for RgbValue {
    fn from(value: HsvValue) -> Self {
        let h = value.h() / 60f32;
        let s = value.s();
        let v = value.v();

        if s == 0f32 {
            return Self::from_dec(v, v, v);
        }

        let i = h.trunc() as u16;
        let f = h - i as f32;

        let p = v * (1f32 - s);
        let q = v * (1f32 - s * f);
        let t = v * (1f32 - s * (1f32 - f));

        match i {
            0 => Self::from_dec(v, t, p),
            1 => Self::from_dec(q, v, p),
            2 => Self::from_dec(p, v, t),
            3 => Self::from_dec(p, q, v),
            4 => Self::from_dec(t, p, v),
            _ => Self::from_dec(v, p, q),
        }
    }
}

impl From<u32> for RgbValue {
    fn from(value: u32) -> Self {
        let r = (value >> u8::BITS * 2) as u8;
        let g = (value >> u8::BITS) as u8;
        let b = value as u8;

        Self(r, g, b)
    }
}

impl From<(u8, u8, u8)> for RgbValue {
    fn from(value: (u8, u8, u8)) -> Self {
        Self(value.0, value.1, value.2)
    }
}

impl From<RgbValue> for u32 {
    fn from(value: RgbValue) -> Self {
        let (r, g, b) = value.into();
        0u32 | (r as u32) << (u8::BITS * 2) | (g as u32) << u8::BITS | b as u32
    }
}

impl From<RgbValue> for (u8, u8, u8) {
    fn from(value: RgbValue) -> Self {
        (value.0, value.1, value.2)
    }
}

#[derive(AproxEq, Clone, Copy, Debug, PartialEq)]
pub struct HsvValue(f32, f32, f32);

impl HsvValue {
    /// Creates a new `HsvValue` given hue, saturation, and value values. When
    /// stored the given values are clamped between `0f32` and `1f32`, except
    /// the hue value which is between `0f32` and `360f32`. If a value is `NaN`
    /// then it is set to `0f32`.
    #[inline]
    #[must_use]
    pub fn new(h: f32, s: f32, v: f32) -> Self {
        Self(
            match h.is_nan() {
                true => 0f32,
                false => h.clamp(0f32, 360f32),
            },
            match s.is_nan() {
                true => 0f32,
                false => s.clamp(0f32, 1f32),
            },
            match v.is_nan() {
                true => 0f32,
                false => v.clamp(0f32, 1f32),
            },
        )
    }

    /// Gets the hue component of the `HsvValue`.
    #[inline]
    #[must_use]
    pub fn h(&self) -> f32 {
        self.0
    }

    /// Gets the saturation component of the `HsvValue`.
    #[inline]
    #[must_use]
    pub fn s(&self) -> f32 {
        self.1
    }

    /// Gets the value component of the `HsvValue`.
    #[inline]
    #[must_use]
    pub fn v(&self) -> f32 {
        self.2
    }

    /// Set this `HsvValue`'s hue component to the given value. Any given value
    /// will be clamped between `0f32` and `360f32` or set to `0f32` it is
    /// `NaN`.
    #[inline]
    pub fn set_h(&mut self, h: f32) {
        match h.is_nan() {
            true => self.0 = 0f32,
            false => self.0 = h.clamp(0f32, 360f32),
        }
    }

    /// Set this `HsvValue`'s green component to the given value. Any given
    /// value will be clamped between `0f32` and `1f32` or set to `0f32` it is
    /// `NaN`.
    #[inline]
    pub fn set_s(&mut self, s: f32) {
        match s.is_nan() {
            true => self.1 = 0f32,
            false => self.1 = s.clamp(0f32, 1f32),
        }
    }

    /// Set this `HsvValue`'s blue component to the given value. Any given value
    /// will be clamped between `0f32` and `1f32` or set to `0f32` it is `NaN`.
    #[inline]
    pub fn set_v(&mut self, v: f32) {
        match v.is_nan() {
            true => self.2 = 0f32,
            false => self.2 = v.clamp(0f32, 1f32),
        }
    }
}

impl From<RgbValue> for HsvValue {
    fn from(value: RgbValue) -> Self {
        /// Changes a `u8` to an `f32` between `0f32` and `1f32`.
        macro_rules! norm {
            ($n:expr) => {
                $n as f32 / 255f32
            };
        }

        let (r, g, b) = value.into();
        let max = r.max(g).max(b);
        let min = r.min(g).min(b);

        if max == 0 {
            return Self::new(0f32, 0f32, 0f32);
        }

        let s = (norm!(max) - norm!(min)) / norm!(max);

        if s == 0f32 {
            return Self::new(0f32, 0f32, (max as f32) / 255f32);
        }

        let h = {
            if max == r {
                (0f32 * 360f32 / 3f32)
                    + (360f32 / 6f32) * (norm!(g) - norm!(b)) / (norm!(max) - norm!(min))
            } else if max == g {
                (1f32 * 360f32 / 3f32)
                    + (360f32 / 6f32) * (norm!(b) - norm!(r)) / (norm!(max) - norm!(min))
            } else {
                (2f32 * 360f32 / 3f32)
                    + (360f32 / 6f32) * (norm!(r) - norm!(g)) / (norm!(max) - norm!(min))
            }
        };

        Self::new(h, s, norm!(max))
    }
}

#[cfg(test)]
mod tests {
    use super::Color;
    use aprox_eq::assert_aprox_eq;

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
