// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Basic floating-point number distributions

use core::mem;
use Rng;
use distributions::{Distribution, Uniform};

/// Generate a floating point number in the half-open interval `[0, 1)` with a
/// uniform distribution.
///
/// This is different from `Uniform` in that it uses all 32 bits of an RNG for a
/// `f32`, instead of only 23, the number of bits that fit in a floats fraction
/// (or 64 instead of 52 bits for a `f64`).
///
/// The smallest interval between values that can be generated is 2^-32
/// (2.3283064e-10) for `f32`, and 2^-64 (5.421010862427522e-20) for `f64`.
/// But this interval increases further away from zero because of limitations of
/// the floating point format. Close to 1.0 the interval is 2^-24 (5.9604645e-8)
/// for `f32`, and 2^-53 (1.1102230246251565) for `f64`. Compare this with
/// `Uniform`, which has a fixed interval of 2^23 and 2^-52 respectively.
///
/// Note: in the future this may change change to request even more bits from
/// the RNG if the value gets very close to 0.0, so it always has as many digits
/// of precision as the float can represent.
///
/// # Example
/// ```rust
/// use rand::{NewRng, SmallRng, Rng};
/// use rand::distributions::HighPrecision01;
///
/// let val: f32 = SmallRng::new().sample(HighPrecision01);
/// println!("f32 from [0,1): {}", val);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct HighPrecision01;

pub(crate) trait IntoFloat {
    type F;

    /// Helper method to combine the fraction and a contant exponent into a
    /// float.
    ///
    /// Only the least significant bits of `self` may be set, 23 for `f32` and
    /// 52 for `f64`.
    /// The resulting value will fall in a range that depends on the exponent.
    /// As an example the range with exponent 0 will be
    /// [2<sup>0</sup>..2<sup>1</sup>), which is [1..2).
    #[inline(always)]
    fn into_float_with_exponent(self, exponent: i32) -> Self::F;
}

macro_rules! float_impls {
    ($ty:ty, $uty:ty, $fraction_bits:expr, $exponent_bias:expr,
     $next_u:ident) => {
        impl IntoFloat for $uty {
            type F = $ty;
            #[inline(always)]
            fn into_float_with_exponent(self, exponent: i32) -> $ty {
                // The exponent is encoded using an offset-binary representation
                let exponent_bits =
                    (($exponent_bias + exponent) as $uty) << $fraction_bits;
                unsafe { mem::transmute(self | exponent_bits) }
            }
        }

        impl Distribution<$ty> for Uniform {
            /// Generate a floating point number in the open interval `(0, 1)`
            /// (not including either endpoint) with a uniform distribution.
            ///
            /// # Example
            /// ```rust
            /// use rand::{NewRng, SmallRng, Rng};
            /// use rand::distributions::Uniform;
            ///
            /// let val: f32 = SmallRng::new().sample(Uniform);
            /// println!("f32 from (0,1): {}", val);
            /// ```
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                const EPSILON: $ty = 1.0 / (1u64 << $fraction_bits) as $ty;
                let float_size = mem::size_of::<$ty>() * 8;

                let value = rng.$next_u();
                let fraction = value >> (float_size - $fraction_bits);
                fraction.into_float_with_exponent(0) - (1.0 - EPSILON / 2.0)
            }
        }

        impl Distribution<$ty> for HighPrecision01 {
            /// Generate a floating point number in the half-open interval
            /// `[0, 1)` with a uniform distribution.
            ///
            /// This is different from `Uniform` in that it uses all 32 bits
            /// of an RNG for a `f32`, instead of only 23, the number of bits
            /// that fit in a floats fraction (or 64 instead of 52 bits for a
            /// `f64`).
            ///
            /// # Example
            /// ```rust
            /// use rand::{NewRng, SmallRng, Rng};
            /// use rand::distributions::HighPrecision01;
            ///
            /// let val: f32 = SmallRng::new().sample(HighPrecision01);
            /// println!("f32 from [0,1): {}", val);
            /// ```
            ///
            /// # Algorithm
            /// (Note: this description used values that apply to `f32` to
            /// illustrate the algorithm).
            ///
            /// The trick to generate a uniform distribution over [0,1) is to
            /// set the exponent to the -log2 of the remaining random bits. A
            /// simpler alternative to -log2 is to count the number of trailing
            /// zero's of the random bits.
            ///
            /// Each exponent is responsible for a piece of the distribution
            /// between [0,1). The exponent -1 fills the part [0.5,1). -2 fills
            /// [0.25,0.5). The lowest exponent we can get is -10. So a problem
            /// with this method is that we can not fill the part between zero
            /// and the part from -10. The solution is to treat numbers with an
            /// exponent of -10 as if they have -9 as exponent, and substract
            /// 2^-9 (implemented in the `fallback` function).
            #[inline]
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                #[inline(never)]
                fn fallback(fraction: $uty) -> $ty {
                    let float_size = (mem::size_of::<$ty>() * 8) as i32;
                    let min_exponent = $fraction_bits as i32 - float_size;
                    let adjust = // 2^MIN_EXPONENT
                        (0 as $uty).into_float_with_exponent(min_exponent);
                    fraction.into_float_with_exponent(min_exponent) - adjust
                }

                let fraction_mask = (1 << $fraction_bits) - 1;
                let value = rng.$next_u();

                let fraction = value & fraction_mask;
                let remaining = value >> $fraction_bits;
                // If `remaing ==0` we end up in the lowest exponent, which
                // needs special treatment.
                if remaining == 0 { return fallback(fraction) }
                let exp = remaining.trailing_zeros() as i32 + 1;
                fraction.into_float_with_exponent(-exp)
            }
        }
    }
}
float_impls! { f32, u32, 23, 127, next_u32 }
float_impls! { f64, u64, 52, 1023, next_u64 }


#[cfg(test)]
mod tests {
    use Rng;
    use mock::StepRng;
    use super::HighPrecision01;

    const EPSILON32: f32 = ::core::f32::EPSILON;
    const EPSILON64: f64 = ::core::f64::EPSILON;

    #[test]
    fn floating_point_edge_cases() {
        let mut zeros = StepRng::new(0, 0);
        assert_eq!(zeros.gen::<f32>(), 0.0 + EPSILON32 / 2.0);
        assert_eq!(zeros.gen::<f64>(), 0.0 + EPSILON64 / 2.0);

        let mut one = StepRng::new(1 << 9, 0);
        let one32 = one.gen::<f32>();
        assert!(EPSILON32 < one32 && one32 < EPSILON32 * 2.0);

        let mut one = StepRng::new(1 << 12, 0);
        let one64 = one.gen::<f64>();
        assert!(EPSILON64 < one64 && one64 < EPSILON64 * 2.0);

        let mut max = StepRng::new(!0, 0);
        assert_eq!(max.gen::<f32>(), 1.0 - EPSILON32 / 2.0);
        assert_eq!(max.gen::<f64>(), 1.0 - EPSILON64 / 2.0);
    }

    #[test]
    fn high_precision_01_edge_cases() {
        // Test that the distribution is a half-open range over [0,1).
        // These constants happen to generate the lowest and highest floats in
        // the range.
        let mut zeros = StepRng::new(0, 0);
        assert_eq!(zeros.sample::<f32, _>(HighPrecision01), 0.0);
        assert_eq!(zeros.sample::<f64, _>(HighPrecision01), 0.0);

        let mut ones = StepRng::new(0xffff_ffff_ffff_ffff, 0);
        assert_eq!(ones.sample::<f32, _>(HighPrecision01), 0.99999994);
        assert_eq!(ones.sample::<f64, _>(HighPrecision01), 0.9999999999999999);
    }
}
