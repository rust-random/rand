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

use core::{cmp, mem};
use Rng;
use distributions::{Distribution, Uniform};

/// Generate a floating point number in the half-open interval `[0, 1)` with a
/// uniform distribution, with as much precision as the floating-point type
/// can represent, including sub-normals.
///
/// Technically 0 is representable, but the probability of occurrence is
/// remote (1 in 2^149 for `f32` or 1 in 2^1074 for `f64`).
///
/// This is different from `Uniform` in that it uses as many random bits as
/// required to get high precision close to 0. Normally only a single call to
/// the source RNG is required (32 bits for `f32` or 64 bits for `f64`); 1 in
/// 2^9 (`f32`) or 2^12 (`f64`) samples need an extra call; of these 1 in 2^32
/// or 1 in 2^64 require a third call, etc.; i.e. even for `f32` a third call is
/// almost impossible to observe with an unbiased RNG. Due to the extra logic
/// there is some performance overhead relative to `Uniform`; this is more
/// significant for `f32` than for `f64`.
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
            /// `[0, 1)` with a uniform distribution. See [`HighPrecision01`].
            ///
            /// # Algorithm
            /// (Note: this description used values that apply to `f32` to
            /// illustrate the algorithm).
            ///
            /// The trick to generate a uniform distribution over [0,1) is to
            /// set the exponent to the -log2 of the remaining random bits. A
            /// simpler alternative to -log2 is to count the number of trailing
            /// zeros in the random bits. In the case where all bits are zero,
            /// we simply generate a new random number and add the number of
            /// trailing zeros to the previous count (up to maximum exponent).
            ///
            /// Each exponent is responsible for a piece of the distribution
            /// between [0,1). We take the above exponent, add 1 and negate;
            /// thus with probability 1/2 we have exponent -1 which fills the
            /// range [0.5,1); with probability 1/4 we have exponent -2 which
            /// fills the range [0.25,0.5), etc. If the exponent reaches the
            /// minimum allowed, the floating-point format drops the implied
            /// fraction bit, thus allowing numbers down to 0 to be sampled.
            ///
            /// [`HighPrecision01`]: struct.HighPrecision01.html
            #[inline]
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                // Unusual case. Separate function to allow inlining of rest.
                #[inline(never)]
                fn fallback<R: Rng + ?Sized>(mut exp: i32, fraction: $uty, rng: &mut R) -> $ty {
                    // Performance impact of code here is negligible.
                    let bits = rng.gen::<$uty>();
                    exp += bits.trailing_zeros() as i32;
                    // If RNG were guaranteed unbiased we could skip the
                    // check against exp; unfortunately it may be.
                    // Worst case ("zeros" RNG) has recursion depth 16.
                    if bits == 0 && exp < $exponent_bias {
                        return fallback(exp, fraction, rng);
                    }
                    exp = cmp::min(exp, $exponent_bias);
                    fraction.into_float_with_exponent(-exp)
                }

                let fraction_mask = (1 << $fraction_bits) - 1;
                let value = rng.$next_u();

                let fraction = value & fraction_mask;
                let remaining = value >> $fraction_bits;
                if remaining == 0 {
                    // exp is compile-time constant so this reduces to a function call:
                    let size_bits = (mem::size_of::<$ty>() * 8) as i32;
                    let exp = (size_bits - $fraction_bits as i32) + 1;
                    return fallback(exp, fraction, rng);
                }

                // Usual case: exponent from -1 to -9 (f32) or -12 (f64)
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
    use {Rng};
    use distributions::HighPrecision01;
    use mock::StepRng;

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

    #[cfg(feature="std")] mod mean {
        use {Rng, SmallRng, SeedableRng, thread_rng};
        use distributions::{Uniform, HighPrecision01};

        macro_rules! test_mean {
            ($name:ident, $ty:ty, $distr:expr) => {
        #[test]
        fn $name() {
            // TODO: no need to &mut here:
            let mut rng = SmallRng::from_rng(&mut thread_rng()).unwrap();
            let mut total: $ty = 0.0;
            const N: u32 = 1_000_000;
            for _ in 0..N {
                total += rng.sample::<$ty, _>($distr);
            }
            let avg = total / (N as $ty);
            //println!("average over {} samples: {}", N, avg);
            assert!(0.499 < avg && avg < 0.501);
        }
        } }

        test_mean!(test_mean_f32, f32, Uniform);
        test_mean!(test_mean_f64, f64, Uniform);
        test_mean!(test_mean_high_f32, f32, HighPrecision01);
        test_mean!(test_mean_high_f64, f64, HighPrecision01);
    }
}
