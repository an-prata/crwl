// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use crate::serial;
use aprox_eq::AproxEq;
use std::u8;

/// A color that can be stored and represented in different ways.
///
/// Because this enum must be stored in memory with the size of the largest of
/// its members it is most efficient to store colors as [`RgbValue`] instances
/// without the [`Color`] enum.
///
/// [`RgbValue`]: RgbValue
/// [`Color`]: Color
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
        match value {
            Color::Rgb(v) => v,
            Color::Hsv(v) => v.into(),
        }
        .into()
    }
}

impl From<u32> for Color {
    fn from(value: u32) -> Self {
        value.into()
    }
}

impl AproxEq for Color {
    fn aprox_eq(&self, other: &Self) -> bool {
        let hsv0 = match self {
            Color::Rgb(c) => c.clone().into(),
            Color::Hsv(c) => c.clone(),
        };

        let hsv1 = match other {
            Color::Rgb(c) => c.clone().into(),
            Color::Hsv(c) => c.clone(),
        };

        hsv0.aprox_eq(&hsv1)
    }
}

/// Represents an RGB color.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct RgbValue {
    pub r: u8,
    pub g: u8,
    pub b: u8,
}

impl RgbValue {
    /// Create a new [`RgbValue`] from the given values.
    ///
    /// [`RgbValue`]: RgbValue
    pub fn new(r: u8, g: u8, b: u8) -> Self {
        Self { r, g, b }
    }

    /// Creates a new [`RgbValue`] given decimal values assumed to be between
    /// `0f32` and `1f32`. All given values are cast to `u8`.
    ///
    /// [`RgbValue`]: RgbValue
    pub fn from_dec(r: f32, g: f32, b: f32) -> Self {
        Self {
            r: (r * 255f32) as u8,
            g: (g * 255f32) as u8,
            b: (b * 255f32) as u8,
        }
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

        Self { r, g, b }
    }
}

impl From<(u8, u8, u8)> for RgbValue {
    fn from(value: (u8, u8, u8)) -> Self {
        Self {
            r: value.0,
            g: value.1,
            b: value.2,
        }
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
        (value.r, value.g, value.b)
    }
}

/// A color as represented with HSV. This stuct guarantees that its contents are
/// a valid color and contains no infinite values or `NaN` values.
#[derive(AproxEq, Clone, Copy, Debug, PartialEq)]
pub struct HsvValue(f32, f32, f32);

impl HsvValue {
    /// Creates a new [`HsvValue`] given hue, saturation, and value values. When
    /// stored the given values are clamped between `0f32` and `1f32`, except
    /// the hue value which is between `0f32` and `360f32`. If a value is `NaN`
    /// then it is set to `0f32`.
    ///
    /// [`HsvValue`]: HsvValue
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

    /// Gets the hue component of the [`HsvValue`].
    ///
    /// [`HsvValue`]: HsvValue
    #[inline]
    #[must_use]
    pub fn h(&self) -> f32 {
        self.0
    }

    /// Gets the saturation component of the [`HsvValue`].
    ///
    /// [`HsvValue`]: HsvValue
    #[inline]
    #[must_use]
    pub fn s(&self) -> f32 {
        self.1
    }

    /// Gets the value component of the [`HsvValue`].
    ///
    /// [`HsvValue`]: HsvValue
    #[inline]
    #[must_use]
    pub fn v(&self) -> f32 {
        self.2
    }

    /// Set this [`HsvValue`]'s hue component to the given value. Any given
    /// value will be clamped between `0f32` and `360f32` or set to `0f32` it is
    /// `NaN`.
    ///
    /// [`HsvValue`]: HsvValue
    #[inline]
    pub fn set_h(&mut self, h: f32) {
        match h.is_nan() {
            true => self.0 = 0f32,
            false => self.0 = h.clamp(0f32, 360f32),
        }
    }

    /// Set this [`HsvValue`]'s saturation component to the given value. Any
    /// given value will be clamped between `0f32` and `1f32` or set to `0f32`
    /// it is `NaN`.
    ///
    /// [`HsvValue`]: HsvValue
    #[inline]
    pub fn set_s(&mut self, s: f32) {
        match s.is_nan() {
            true => self.1 = 0f32,
            false => self.1 = s.clamp(0f32, 1f32),
        }
    }

    /// Set this [`HsvValue`]'s value component to the given value. Any given
    /// value will be clamped between `0f32` and `1f32` or set to `0f32` it is
    /// `NaN`.
    ///
    /// [`HsvValue`]: HsvValue
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
    use super::{Color, HsvValue, RgbValue};
    use aprox_eq::assert_aprox_eq;

    #[test]
    pub fn hsv_to_rgb() {
        let color_pairs = [
            (
                Color::Rgb(RgbValue::new(255u8, 0u8, 0u8)),
                Color::Hsv(HsvValue::new(0f32, 1f32, 1f32)),
            ),
            (
                Color::Rgb(RgbValue::new(0u8, 255u8, 0u8)),
                Color::Hsv(HsvValue::new(120f32, 1f32, 1f32)),
            ),
            (
                Color::Rgb(RgbValue::from_dec(0f32, 0f32, 1f32)),
                Color::Hsv(HsvValue::new(240f32, 1f32, 1f32)),
            ),
            (
                Color::Rgb(RgbValue::from_dec(0f32, 0f32, 0f32)),
                Color::Hsv(HsvValue::new(0f32, 0f32, 0f32)),
            ),
        ];

        for (rgb, hsv) in color_pairs {
            assert_aprox_eq!(rgb, hsv);

            let rgb = match rgb {
                Color::Rgb(v) => v,
                Color::Hsv(_) => panic!("expected `RgbValue`"),
            };

            let hsv = match hsv {
                Color::Rgb(_) => panic!("expected `HsvValue`"),
                Color::Hsv(v) => v,
            };

            assert_eq!(rgb, hsv.into());
            assert_aprox_eq!(<RgbValue as Into<HsvValue>>::into(rgb), hsv);
        }
    }
}
