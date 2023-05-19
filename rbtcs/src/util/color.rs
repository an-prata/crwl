// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use crate::serial;
use aprox_eq::AproxEq;
use std::u8;

// Conversions (all conversions are communative):
//
// (u8, u8, u8) <-> RgbValue
// (u8, u8, u8) <-> RgbFloatValue
//
// (f32, f32, f32) <-> RgbValue
// (f32, f32, f32) <-> RgbFloatValue
// (f32, f32, f32) <-> HsvValue
//
// u32 <-> RgbValue
// u32 <-> RgbFloatValue
// u32 <-> HsvValue
//
// RgbValue <-> RgbFloatValue
// RgbValue <-> HsvValue
// HsvValue <-> RgbFloatValue

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
    RgbFloat(RgbFloatValue),
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

impl From<u32> for Color {
    fn from(value: u32) -> Self {
        value.into()
    }
}

impl AproxEq for Color {
    fn aprox_eq(&self, other: &Self) -> bool {
        let hsv0 = match self {
            Color::Rgb(c) => c.clone().into(),
            Color::RgbFloat(c) => c.clone().into(),
            Color::Hsv(c) => c.clone(),
        };

        let hsv1 = match other {
            Color::Rgb(c) => c.clone().into(),
            Color::RgbFloat(c) => c.clone().into(),
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

    /// Gets a byte representation of this [`RgbValue`] in the order red, green,
    /// then blue.
    ///
    /// [`RgbValue`]: RgbValue
    #[inline]
    #[must_use]
    pub fn bytes(&self) -> [u8; 3] {
        [self.r, self.g, self.b]
    }
}

// `IntoIterator` is implemented instead of `Iterator` to save the `i8` when not
// iterating.
impl IntoIterator for RgbValue {
    type Item = u8;
    type IntoIter = RgbIntoIter<u8>;

    /// Creates an [`Iterator`] for iterating over the elements of an
    /// [`RgbValue`] in the order red, green, then blue. Intended for applying
    /// things like brightness effects.
    ///
    /// [`Iterator`]: Iterator
    /// [`RgbValue`]: RgbValue
    fn into_iter(self) -> Self::IntoIter {
        RgbIntoIter::new(self.bytes())
    }
}

impl From<RgbFloatValue> for RgbValue {
    fn from(value: RgbFloatValue) -> Self {
        Self {
            r: (value.r() * (u8::MAX as f32)) as u8,
            g: (value.g() * (u8::MAX as f32)) as u8,
            b: (value.b() * (u8::MAX as f32)) as u8,
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

impl From<(f32, f32, f32)> for RgbValue {
    fn from(value: (f32, f32, f32)) -> Self {
        RgbFloatValue::from(value).into()
    }
}

impl From<HsvValue> for RgbValue {
    fn from(value: HsvValue) -> Self {
        RgbFloatValue::from(value).into()
    }
}

/// Like [`RgbValue`] in that it represents a color using RGB, but stores its
/// values as 32 bit floating point numbers between `0f32` and `1f32`.
///
/// [`RgbValue`]: RgbValue
#[derive(AproxEq, Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct RgbFloatValue(f32, f32, f32);

impl RgbFloatValue {
    /// Creates a new [`RgbFloatValue`] using the given values. All given values
    /// are made `0f32` if they are `NaN` and clamped between `0f32` and `1f32`
    /// if they are not.
    ///
    /// [`RgbFloatValue`]: RgbFloatValue
    pub fn new(r: f32, g: f32, b: f32) -> Self {
        Self(
            match r.is_nan() {
                true => 0f32,
                false => r.clamp(0f32, 1f32),
            },
            match g.is_nan() {
                true => 0f32,
                false => g.clamp(0f32, 1f32),
            },
            match b.is_nan() {
                true => 0f32,
                false => b.clamp(0f32, 1f32),
            },
        )
    }

    /// Gets the red component of the given [`RgbFloatValue`]. This value will
    /// always be between `0f32` and `1f32`.
    #[inline]
    #[must_use]
    pub fn r(&self) -> f32 {
        self.0
    }

    /// Sets the given red value of the given [`RgbFloatValue`]. The given value
    /// will be made `0f32` if it is `NaN` and clamped betwee `0f32` and `1f32`
    /// if it is not.
    #[inline]
    pub fn set_r(&mut self, r: f32) -> &mut Self {
        self.0 = match r.is_nan() {
            true => 0f32,
            false => r.clamp(0f32, 1f32),
        };

        self
    }

    /// Gets the green component of the given [`RgbFloatValue`]. This value will
    /// always be between `0f32` and `1f32`.
    #[inline]
    #[must_use]
    pub fn g(&self) -> f32 {
        self.1
    }

    /// Sets the given green value of the given [`RgbFloatValue`]. The given
    /// value will be made `0f32` if it is `NaN` and clamped betwee `0f32` and
    /// `1f32` if it is not.
    #[inline]
    pub fn set_g(&mut self, g: f32) -> &mut Self {
        self.1 = match g.is_nan() {
            true => 0f32,
            false => g.clamp(0f32, 1f32),
        };

        self
    }

    /// Gets the blue component of the given [`RgbFloatValue`]. This value will
    /// always be between `0f32` and `1f32`.
    #[inline]
    #[must_use]
    pub fn b(&self) -> f32 {
        self.2
    }

    /// Sets the given blue value of the given [`RgbFloatValue`]. The given
    /// value will be made `0f32` if it is `NaN` and clamped betwee `0f32` and
    /// `1f32` if it is not.
    #[inline]
    pub fn set_b(&mut self, b: f32) -> &mut Self {
        self.2 = match b.is_nan() {
            true => 0f32,
            false => b.clamp(0f32, 1f32),
        };

        self
    }
}

impl From<RgbValue> for RgbFloatValue {
    fn from(value: RgbValue) -> Self {
        Self(
            (value.r as f32) / (u8::MAX as f32),
            (value.g as f32) / (u8::MAX as f32),
            (value.b as f32) / (u8::MAX as f32),
        )
    }
}

impl IntoIterator for RgbFloatValue {
    type Item = f32;
    type IntoIter = RgbIntoIter<f32>;

    fn into_iter(self) -> Self::IntoIter {
        RgbIntoIter::new([self.0, self.1, self.2])
    }
}

impl From<u32> for RgbFloatValue {
    fn from(value: u32) -> Self {
        RgbValue::from(value).into()
    }
}

impl From<(u8, u8, u8)> for RgbFloatValue {
    fn from(value: (u8, u8, u8)) -> Self {
        RgbValue::from(value).into()
    }
}

impl From<(f32, f32, f32)> for RgbFloatValue {
    fn from((r, g, b): (f32, f32, f32)) -> Self {
        Self(r, g, b)
    }
}

impl From<HsvValue> for RgbFloatValue {
    fn from(value: HsvValue) -> Self {
        let h = value.h() / 60f32;
        let s = value.s();
        let v = value.v();

        if s == 0f32 {
            return Self::new(v, v, v);
        }

        let i = h.trunc() as u16;
        let f = h - i as f32;

        let p = v * (1f32 - s);
        let q = v * (1f32 - s * f);
        let t = v * (1f32 - s * (1f32 - f));

        match i {
            0 => Self::new(v, t, p),
            1 => Self::new(q, v, p),
            2 => Self::new(p, v, t),
            3 => Self::new(p, q, v),
            4 => Self::new(t, p, v),
            _ => Self::new(v, p, q),
        }
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

/// Type returned by [`into_iter`] as implemented by [`RgbValue`].
///
/// [`into_iter`]: IntoIterator::into_iter()
/// [`RgbValue`]: RgbValue
pub struct RgbIntoIter<T>
where
    T: Copy,
{
    rgb: [T; 3],
    i: usize,
}

impl<T> RgbIntoIter<T>
where
    T: Copy,
{
    /// Creates a new [`RgbIntoIter`] for iterating over an [`RgbValue`].
    ///
    /// [`RgbIntoIter`]: RgbIntoIter
    /// [`RgbValue`]: RgbValue
    pub fn new(rgb: [T; 3]) -> Self {
        Self { rgb, i: usize::MAX }
    }
}

impl<T> Iterator for RgbIntoIter<T>
where
    T: Copy,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        // The `i` value here will overflow on the first call of this function
        // and roll back to `0`.
        self.i += 1;

        match self.i > self.rgb.len() {
            true => None,
            false => Some(self.rgb[self.i]),
        }
    }
}

impl From<RgbValue> for HsvValue {
    fn from(value: RgbValue) -> Self {
        RgbFloatValue::from(value).into()
    }
}

impl From<RgbFloatValue> for HsvValue {
    fn from(value: RgbFloatValue) -> Self {
        let (r, g, b): (f32, f32, f32) = value.into();
        let max = r.max(g).max(b);
        let min = r.min(g).min(b);

        if max == 0f32 {
            return Self::new(0f32, 0f32, 0f32);
        }

        let s = (max - min) / max;

        if s == 0f32 {
            return Self::new(0f32, 0f32, (max as f32) / 255f32);
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

        Self::new(h, s, max)
    }
}

impl From<u32> for HsvValue {
    fn from(value: u32) -> Self {
        RgbValue::from(value).into()
    }
}

impl From<(f32, f32, f32)> for HsvValue {
    fn from((r, g, b): (f32, f32, f32)) -> Self {
        Self(r, g, b)
    }
}

// external impls:

impl From<Color> for u32 {
    fn from(value: Color) -> Self {
        match value {
            Color::Rgb(v) => v,
            Color::RgbFloat(v) => v.into(),
            Color::Hsv(v) => v.into(),
        }
        .into()
    }
}

impl From<RgbValue> for u32 {
    fn from(value: RgbValue) -> Self {
        let (r, g, b): (u8, u8, u8) = value.into();
        0u32 | (r as u32) << (u8::BITS * 2) | (g as u32) << u8::BITS | b as u32
    }
}

impl From<RgbValue> for (u8, u8, u8) {
    fn from(value: RgbValue) -> Self {
        (value.r, value.g, value.b)
    }
}

impl From<RgbValue> for (f32, f32, f32) {
    fn from(value: RgbValue) -> Self {
        RgbFloatValue::from(value).into()
    }
}

impl From<RgbFloatValue> for u32 {
    fn from(value: RgbFloatValue) -> Self {
        RgbValue::from(value).into()
    }
}

impl From<RgbFloatValue> for (u8, u8, u8) {
    fn from(value: RgbFloatValue) -> Self {
        RgbValue::from(value).into()
    }
}

impl From<RgbFloatValue> for (f32, f32, f32) {
    fn from(value: RgbFloatValue) -> Self {
        (value.0, value.1, value.2)
    }
}

impl From<HsvValue> for u32 {
    fn from(value: HsvValue) -> Self {
        RgbValue::from(value).into()
    }
}

impl From<HsvValue> for (f32, f32, f32) {
    fn from(value: HsvValue) -> Self {
        (value.0, value.1, value.2)
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
                Color::Rgb(RgbValue::from((0f32, 0f32, 1f32))),
                Color::Hsv(HsvValue::new(240f32, 1f32, 1f32)),
            ),
            (
                Color::Rgb(RgbValue::from((0f32, 0f32, 0f32))),
                Color::Hsv(HsvValue::new(0f32, 0f32, 0f32)),
            ),
        ];

        for (rgb, hsv) in color_pairs {
            assert_aprox_eq!(rgb, hsv);

            let rgb = match rgb {
                Color::Rgb(v) => v,
                Color::RgbFloat(_) => panic!("expected `RgbValue`"),
                Color::Hsv(_) => panic!("expected `RgbValue`"),
            };

            let hsv = match hsv {
                Color::Rgb(_) => panic!("expected `HsvValue`"),
                Color::RgbFloat(_) => panic!("expected `RgbValue`"),
                Color::Hsv(v) => v,
            };

            assert_eq!(rgb, hsv.into());
            assert_aprox_eq!(<RgbValue as Into<HsvValue>>::into(rgb), hsv);
        }
    }
}
