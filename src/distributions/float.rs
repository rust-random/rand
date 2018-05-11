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
use distributions::{Distribution, Standard};

/// A distribution to sample floating point numbers uniformly in the half-open
/// interval `(0, 1]`, i.e. including 1 but not 0.
///
/// All values that can be generated are of the form `n * ε/2`. For `f32`
/// the 23 most significant random bits of a `u32` are used and for `f64` the
/// 53 most significant bits of a `u64` are used. The conversion uses the
/// multiplicative method.
///
/// See also: [`Standard`] which samples from `[0, 1)`, [`Open01`]
/// which samples from `(0, 1)` and [`Uniform`] which samples from arbitrary
/// ranges.
///
/// # Example
/// ```
/// use rand::{thread_rng, Rng};
/// use rand::distributions::OpenClosed01;
///
/// let val: f32 = thread_rng().sample(OpenClosed01);
/// println!("f32 from (0, 1): {}", val);
/// ```
///
/// [`Standard`]: struct.Standard.html
/// [`Open01`]: struct.Open01.html
/// [`Uniform`]: uniform/struct.Uniform.html
#[derive(Clone, Copy, Debug)]
pub struct OpenClosed01;

/// A distribution to sample floating point numbers uniformly in the open
/// interval `(0, 1)`, i.e. not including either endpoint.
///
/// All values that can be generated are of the form `n * ε + ε/2`. For `f32`
/// the 22 most significant random bits of an `u32` are used, for `f64` 52 from
/// an `u64`. The conversion uses a transmute-based method.
///
/// See also: [`Standard`] which samples from `[0, 1)`, [`OpenClosed01`]
/// which samples from `(0, 1]` and [`Uniform`] which samples from arbitrary
/// ranges.
///
/// # Example
/// ```
/// use rand::{thread_rng, Rng};
/// use rand::distributions::Open01;
///
/// let val: f32 = thread_rng().sample(Open01);
/// println!("f32 from (0, 1): {}", val);
/// ```
///
/// [`Standard`]: struct.Standard.html
/// [`OpenClosed01`]: struct.OpenClosed01.html
/// [`Uniform`]: uniform/struct.Uniform.html
#[derive(Clone, Copy, Debug)]
pub struct Open01;


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
    fn into_float_with_exponent(self, exponent: i32) -> Self::F;
}

macro_rules! float_impls {
    ($ty:ty, $uty:ty, $fraction_bits:expr, $exponent_bias:expr) => {
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

        impl Distribution<$ty> for Standard {
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                // Multiply-based method; 24/53 random bits; [0, 1) interval.
                // We use the most significant bits because for simple RNGs
                // those are usually more random.
                let float_size = mem::size_of::<$ty>() * 8;
                let precision = $fraction_bits + 1;
                let scale = 1.0 / ((1 as $uty << precision) as $ty);

                let value: $uty = rng.gen();
                scale * (value >> (float_size - precision)) as $ty
            }
        }

        impl Distribution<$ty> for OpenClosed01 {
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                // Multiply-based method; 24/53 random bits; (0, 1] interval.
                // We use the most significant bits because for simple RNGs
                // those are usually more random.
                let float_size = mem::size_of::<$ty>() * 8;
                let precision = $fraction_bits + 1;
                let scale = 1.0 / ((1 as $uty << precision) as $ty);

                let value: $uty = rng.gen();
                let value = value >> (float_size - precision);
                // Add 1 to shift up; will not overflow because of right-shift:
                scale * (value + 1) as $ty
            }
        }

        impl Distribution<$ty> for Open01 {
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                // Transmute-based method; 23/52 random bits; (0, 1) interval.
                // We use the most significant bits because for simple RNGs
                // those are usually more random.
                const EPSILON: $ty = 1.0 / (1u64 << $fraction_bits) as $ty;
                let float_size = mem::size_of::<$ty>() * 8;

                let value: $uty = rng.gen();
                let fraction = value >> (float_size - $fraction_bits);
                fraction.into_float_with_exponent(0) - (1.0 - EPSILON / 2.0)
            }
        }
    }
}
float_impls! { f32, u32, 23, 127 }
float_impls! { f64, u64, 52, 1023 }


#[cfg(test)]
mod tests {
    use Rng;
    use distributions::{Open01, OpenClosed01};
    use rngs::mock::StepRng;

    const EPSILON32: f32 = ::core::f32::EPSILON;
    const EPSILON64: f64 = ::core::f64::EPSILON;

    #[test]
    fn standard_fp_edge_cases() {
        let mut zeros = StepRng::new(0, 0);
        assert_eq!(zeros.gen::<f32>(), 0.0);
        assert_eq!(zeros.gen::<f64>(), 0.0);

        let mut one32 = StepRng::new(1 << 8, 0);
        assert_eq!(one32.gen::<f32>(), EPSILON32 / 2.0);

        let mut one64 = StepRng::new(1 << 11, 0);
        assert_eq!(one64.gen::<f64>(), EPSILON64 / 2.0);

        let mut max = StepRng::new(!0, 0);
        assert_eq!(max.gen::<f32>(), 1.0 - EPSILON32 / 2.0);
        assert_eq!(max.gen::<f64>(), 1.0 - EPSILON64 / 2.0);
    }

    #[test]
    fn openclosed01_edge_cases() {
        let mut zeros = StepRng::new(0, 0);
        assert_eq!(zeros.sample::<f32, _>(OpenClosed01), 0.0 + EPSILON32 / 2.0);
        assert_eq!(zeros.sample::<f64, _>(OpenClosed01), 0.0 + EPSILON64 / 2.0);

        let mut one32 = StepRng::new(1 << 8, 0);
        assert_eq!(one32.sample::<f32, _>(OpenClosed01), EPSILON32);

        let mut one64 = StepRng::new(1 << 11, 0);
        assert_eq!(one64.sample::<f64, _>(OpenClosed01), EPSILON64);

        let mut max = StepRng::new(!0, 0);
        assert_eq!(max.sample::<f32, _>(OpenClosed01), 1.0);
        assert_eq!(max.sample::<f64, _>(OpenClosed01), 1.0);
    }

    #[test]
    fn open01_edge_cases() {
        let mut zeros = StepRng::new(0, 0);
        assert_eq!(zeros.sample::<f32, _>(Open01), 0.0 + EPSILON32 / 2.0);
        assert_eq!(zeros.sample::<f64, _>(Open01), 0.0 + EPSILON64 / 2.0);

        let mut one32 = StepRng::new(1 << 9, 0);
        assert_eq!(one32.sample::<f32, _>(Open01), EPSILON32 / 2.0 * 3.0);

        let mut one64 = StepRng::new(1 << 12, 0);
        assert_eq!(one64.sample::<f64, _>(Open01), EPSILON64 / 2.0 * 3.0);

        let mut max = StepRng::new(!0, 0);
        assert_eq!(max.sample::<f32, _>(Open01), 1.0 - EPSILON32 / 2.0);
        assert_eq!(max.sample::<f64, _>(Open01), 1.0 - EPSILON64 / 2.0);
    }
}
