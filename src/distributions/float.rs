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
use distributions::utils::FloatSIMDUtils;
#[cfg(feature="simd_support")]
use core::simd::*;
use distributions::uniform::{SampleUniform, UniformSampler};

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

/// A distribution to do high precision sampling of floating point numbers
/// uniformly in a given range. This is similar to Uniform, but samples
/// numbers with the full precision of the floating-point type used, at the
/// cost of slower performance.
#[derive(Clone, Copy, Debug)]
pub struct HighPrecision<F> where F: HPFloatHelper {
    low_as_int: F::SignedInt,
    high_as_int: F::SignedInt,
    exponent: u16,
    mantissa_distribution: F::SignedIntDistribution,
}

impl<F: HPFloatHelper> HighPrecision<F> {
    /// Create a new HighPrecision distribution. Sampling from this
    /// distribution will return values `>= low` and `< high`.
    pub fn new(low: F, high: F) -> Self {
        let parsed = F::parse_new(low, high);
        HighPrecision {
            low_as_int: parsed.0,
            high_as_int: parsed.1,
            exponent: parsed.2,
            mantissa_distribution: parsed.3,
        }
    }
}

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

pub trait HPFloatHelper: Sized {
    type SignedInt;
    type SignedIntDistribution;
    fn parse_new(low: Self, high: Self) ->
        (Self::SignedInt, Self::SignedInt, u16, Self::SignedIntDistribution);
}

macro_rules! float_impls {
    ($ty:ident, $uty:ident, $f_scalar:ident, $u_scalar:ty,
     $fraction_bits:expr, $exponent_bias:expr) => {
        impl IntoFloat for $uty {
            type F = $ty;
            #[inline(always)]
            fn into_float_with_exponent(self, exponent: i32) -> $ty {
                // The exponent is encoded using an offset-binary representation
                let exponent_bits: $u_scalar =
                    (($exponent_bias + exponent) as $u_scalar) << $fraction_bits;
                // TODO: use from_bits when min compiler > 1.25 (see #545)
                // $ty::from_bits(self | exponent_bits)
                unsafe{ mem::transmute(self | exponent_bits) }
            }
        }

        impl Distribution<$ty> for Standard {
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                // Multiply-based method; 24/53 random bits; [0, 1) interval.
                // We use the most significant bits because for simple RNGs
                // those are usually more random.
                let float_size = mem::size_of::<$f_scalar>() * 8;
                let precision = $fraction_bits + 1;
                let scale = 1.0 / ((1 as $u_scalar << precision) as $f_scalar);

                let value: $uty = rng.gen();
                let value = value >> (float_size - precision);
                scale * $ty::cast_from_int(value)
            }
        }

        impl Distribution<$ty> for OpenClosed01 {
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                // Multiply-based method; 24/53 random bits; (0, 1] interval.
                // We use the most significant bits because for simple RNGs
                // those are usually more random.
                let float_size = mem::size_of::<$f_scalar>() * 8;
                let precision = $fraction_bits + 1;
                let scale = 1.0 / ((1 as $u_scalar << precision) as $f_scalar);

                let value: $uty = rng.gen();
                let value = value >> (float_size - precision);
                // Add 1 to shift up; will not overflow because of right-shift:
                scale * $ty::cast_from_int(value + 1)
            }
        }

        impl Distribution<$ty> for Open01 {
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                // Transmute-based method; 23/52 random bits; (0, 1) interval.
                // We use the most significant bits because for simple RNGs
                // those are usually more random.
                use core::$f_scalar::EPSILON;
                let float_size = mem::size_of::<$f_scalar>() * 8;

                let value: $uty = rng.gen();
                let fraction = value >> (float_size - $fraction_bits);
                fraction.into_float_with_exponent(0) - (1.0 - EPSILON / 2.0)
            }
        }
    }
}

float_impls! { f32, u32, f32, u32, 23, 127 }
float_impls! { f64, u64, f64, u64, 52, 1023 }

#[cfg(feature="simd_support")]
float_impls! { f32x2, u32x2, f32, u32, 23, 127 }
#[cfg(feature="simd_support")]
float_impls! { f32x4, u32x4, f32, u32, 23, 127 }
#[cfg(feature="simd_support")]
float_impls! { f32x8, u32x8, f32, u32, 23, 127 }
#[cfg(feature="simd_support")]
float_impls! { f32x16, u32x16, f32, u32, 23, 127 }

#[cfg(feature="simd_support")]
float_impls! { f64x2, u64x2, f64, u64, 52, 1023 }
#[cfg(feature="simd_support")]
float_impls! { f64x4, u64x4, f64, u64, 52, 1023 }
#[cfg(feature="simd_support")]
float_impls! { f64x8, u64x8, f64, u64, 52, 1023 }


macro_rules! high_precision_float_impls {
    ($ty:ty, $uty:ty, $ity:ty, $fraction_bits:expr, $exponent_bits:expr) => {
        impl HPFloatHelper for $ty {
            type SignedInt = $ity;
            type SignedIntDistribution = <$ity as SampleUniform>::Sampler;

            fn parse_new(low: $ty, high: $ty) ->
                ($ity, $ity, u16, <$ity as SampleUniform>::Sampler) {
                fn bitmask(bits: $uty) -> $uty {
                    if bits >= ::core::mem::size_of::<$uty>() as $uty * 8 { (-1 as $ity) as $uty } else { (1 as $uty << bits) - 1 }
                }
                fn round_neg_inf_shr(val: $ity, n: u16) -> $ity {
                    if n < ::core::mem::size_of::<$ity>() as u16 * 8 {
                        val >> n
                    } else if val >= 0 {
                        0
                    } else {
                        -1
                    }
                }
                fn round_pos_inf_shr(val: $ity, n: u16) -> $ity {
                    -round_neg_inf_shr(-val, n)
                }
                fn parse(val: $ty) -> ($ity, u16, $ity) {
                    let bits = val.to_bits();
                    let mut mant = (bits & bitmask($fraction_bits)) as $ity;
                    let mut exp = ((bits >> $fraction_bits) & bitmask($exponent_bits)) as u16;
                    let neg = (bits >> ($fraction_bits + $exponent_bits)) == 1;
                    let mut as_int = (bits & bitmask($fraction_bits + $exponent_bits)) as $ity;
                    if exp != 0 {
                        mant |= 1 as $ity << $fraction_bits;
                    } else {
                        exp = 1;
                    }
                    if neg {
                        mant *= -1;
                        as_int *= -1;
                    }
                    (mant, exp, as_int)
                }

                assert!(low.is_finite() && high.is_finite(), "HighPrecision::new called with non-finite limit");
                assert!(low < high, "HighPrecision::new called with low >= high");

                let (mut mant_low, exp_low, low_as_int) = parse(low);
                let (mut mant_high, exp_high, high_as_int) = parse(high);

                let exp;
                if exp_high >= exp_low {
                    exp = exp_high;
                    mant_low = round_neg_inf_shr(mant_low, exp_high - exp_low);
                } else {
                    exp = exp_low;
                    mant_high = round_pos_inf_shr(mant_high, exp_low - exp_high);
                }

                (low_as_int,
                 high_as_int,
                 exp,
                 <$ity as SampleUniform>::Sampler::new(mant_low, mant_high))
            }
        }

        impl Distribution<$ty> for HighPrecision<$ty> {
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                fn bitmask(bits: $uty) -> $uty {
                    if bits >= ::core::mem::size_of::<$uty>() as $uty * 8 { (-1 as $ity) as $uty } else { (1 as $uty << bits) - 1 }
                }
                loop {
                    let signed_mant = self.mantissa_distribution.sample(rng);
                    // Operate on the absolute value so that we can count bit-sizes
                    // correctly
                    let is_neg = signed_mant < 0;
                    let mut mantissa = signed_mant.abs() as $uty;

                    // If the resulting mantissa has too few bits, arithmetically add additional
                    // bits from rng. When `mant` represents a negative number, this means
                    // subtracting the generated bits.
                    const GOAL_ZEROS: u16 = $exponent_bits; // full_size - $fraction_bits - 1 = $exponent_bits
                    let mut exp = self.exponent;
                    let mut zeros = mantissa.leading_zeros() as u16;
                    while zeros > GOAL_ZEROS && exp > 1 {
                        let additional = ::core::cmp::min(zeros - GOAL_ZEROS, exp - 1);
                        let additional_bits = rng.gen::<$uty>() >> (::core::mem::size_of::<$uty>() as u16 * 8 - additional);
                        mantissa <<= additional;
                        if !is_neg {
                            mantissa |= additional_bits;
                        } else {
                            mantissa -= additional_bits;
                        }
                        exp -= additional;
                        zeros = mantissa.leading_zeros() as u16;
                    }

                    // At this point, if we generate and add more bits, we're just
                    // going to have to round them off. Since we round towards negative
                    // infinity, i.e. the opposite direction of the added bits, we'll
                    // just get back to exactly where we are now.

                    // There is an edgecase if the mantissa is negative 0x0010_0000_0000_0000.
                    // While this number is already 53 bits, if we subtract more
                    // geneated bits from this number, we will lose one bit at the top
                    // and get fewer total bits. That means that we can fit an extra
                    // bit at the end, which if it's a zero will prevent rounding from
                    // getting us back to the original value.
                    if mantissa == (1 as $uty << $fraction_bits) && is_neg && exp > 1 && rng.gen::<bool>() {
                        mantissa = bitmask($fraction_bits + 1);
                        exp -= 1;
                    }

                    // Handle underflow values
                    if mantissa < (1 as $uty << $fraction_bits) {
                        debug_assert_eq!(exp, 1);
                        exp = 0;
                    }

                    // Merge exponent and mantissa into final result
                    let mut res = (mantissa & bitmask($fraction_bits)) |
                                  ((exp as $uty) << $fraction_bits);
                    let mut res_as_int = res as $ity;
                    if is_neg {
                        res_as_int *= -1;
                        res |= 1 as $uty << ($fraction_bits + $exponent_bits);
                    }

                    // Check that we're within the requested bounds. These checks can
                    // only fail on the side that was shifted and rounded during
                    // initial parsing.
                    if self.low_as_int <= res_as_int && res_as_int < self.high_as_int {
                        return <$ty>::from_bits(res);
                    }

                    // If not start over. We're avoiding reusing any of the previous
                    // computation in order to avoid introducing bias, and to keep
                    // things simple since this should be rare.

                    // Assert that we got here due to rounding
                    #[cfg(debug_assertions)]
                    {
                        let exp_low = (self.low_as_int.abs() as $uty >> $fraction_bits) & bitmask($exponent_bits);
                        let exp_high = (self.high_as_int.abs() as $uty >> $fraction_bits) & bitmask($exponent_bits);
                        let mant_low = self.low_as_int.abs() as $uty & bitmask($fraction_bits);
                        let mant_high = self.high_as_int.abs() as $uty & bitmask($fraction_bits);
                        if res_as_int < self.low_as_int {
                            assert!(exp_low < exp_high);
                            assert!(mant_low & bitmask(exp_high - exp_low) != 0);
                        }
                        if res_as_int >= self.high_as_int {
                            assert!(exp_high < exp_low);
                            assert!(mant_high & bitmask(exp_low - exp_high) != 0);
                        }
                    }
                }
            }
        }
    }
}

high_precision_float_impls! { f32, u32, i32, 23, 8 }
high_precision_float_impls! { f64, u64, i64, 52, 11 }


#[cfg(test)]
mod tests {
    use Rng;
    use super::*;
    use rngs::mock::StepRng;
    #[cfg(feature="simd_support")]
    use core::simd::*;

    const EPSILON32: f32 = ::core::f32::EPSILON;
    const EPSILON64: f64 = ::core::f64::EPSILON;

    macro_rules! test_f32 {
        ($fnn:ident, $ty:ident, $ZERO:expr, $EPSILON:expr) => {
            #[test]
            fn $fnn() {
                // Standard
                let mut zeros = StepRng::new(0, 0);
                assert_eq!(zeros.gen::<$ty>(), $ZERO);
                let mut one = StepRng::new(1 << 8 | 1 << (8 + 32), 0);
                assert_eq!(one.gen::<$ty>(), $EPSILON / 2.0);
                let mut max = StepRng::new(!0, 0);
                assert_eq!(max.gen::<$ty>(), 1.0 - $EPSILON / 2.0);

                // OpenClosed01
                let mut zeros = StepRng::new(0, 0);
                assert_eq!(zeros.sample::<$ty, _>(OpenClosed01),
                           0.0 + $EPSILON / 2.0);
                let mut one = StepRng::new(1 << 8 | 1 << (8 + 32), 0);
                assert_eq!(one.sample::<$ty, _>(OpenClosed01), $EPSILON);
                let mut max = StepRng::new(!0, 0);
                assert_eq!(max.sample::<$ty, _>(OpenClosed01), $ZERO + 1.0);

                // Open01
                let mut zeros = StepRng::new(0, 0);
                assert_eq!(zeros.sample::<$ty, _>(Open01), 0.0 + $EPSILON / 2.0);
                let mut one = StepRng::new(1 << 9 | 1 << (9 + 32), 0);
                assert_eq!(one.sample::<$ty, _>(Open01), $EPSILON / 2.0 * 3.0);
                let mut max = StepRng::new(!0, 0);
                assert_eq!(max.sample::<$ty, _>(Open01), 1.0 - $EPSILON / 2.0);
            }
        }
    }
    test_f32! { f32_edge_cases, f32, 0.0, EPSILON32 }
    #[cfg(feature="simd_support")]
    test_f32! { f32x2_edge_cases, f32x2, f32x2::splat(0.0), f32x2::splat(EPSILON32) }
    #[cfg(feature="simd_support")]
    test_f32! { f32x4_edge_cases, f32x4, f32x4::splat(0.0), f32x4::splat(EPSILON32) }
    #[cfg(feature="simd_support")]
    test_f32! { f32x8_edge_cases, f32x8, f32x8::splat(0.0), f32x8::splat(EPSILON32) }
    #[cfg(feature="simd_support")]
    test_f32! { f32x16_edge_cases, f32x16, f32x16::splat(0.0), f32x16::splat(EPSILON32) }

    macro_rules! test_f64 {
        ($fnn:ident, $ty:ident, $ZERO:expr, $EPSILON:expr) => {
            #[test]
            fn $fnn() {
                // Standard
                let mut zeros = StepRng::new(0, 0);
                assert_eq!(zeros.gen::<$ty>(), $ZERO);
                let mut one = StepRng::new(1 << 11, 0);
                assert_eq!(one.gen::<$ty>(), $EPSILON / 2.0);
                let mut max = StepRng::new(!0, 0);
                assert_eq!(max.gen::<$ty>(), 1.0 - $EPSILON / 2.0);

                // OpenClosed01
                let mut zeros = StepRng::new(0, 0);
                assert_eq!(zeros.sample::<$ty, _>(OpenClosed01),
                           0.0 + $EPSILON / 2.0);
                let mut one = StepRng::new(1 << 11, 0);
                assert_eq!(one.sample::<$ty, _>(OpenClosed01), $EPSILON);
                let mut max = StepRng::new(!0, 0);
                assert_eq!(max.sample::<$ty, _>(OpenClosed01), $ZERO + 1.0);

                // Open01
                let mut zeros = StepRng::new(0, 0);
                assert_eq!(zeros.sample::<$ty, _>(Open01), 0.0 + $EPSILON / 2.0);
                let mut one = StepRng::new(1 << 12, 0);
                assert_eq!(one.sample::<$ty, _>(Open01), $EPSILON / 2.0 * 3.0);
                let mut max = StepRng::new(!0, 0);
                assert_eq!(max.sample::<$ty, _>(Open01), 1.0 - $EPSILON / 2.0);
            }
        }
    }
    test_f64! { f64_edge_cases, f64, 0.0, EPSILON64 }
    #[cfg(feature="simd_support")]
    test_f64! { f64x2_edge_cases, f64x2, f64x2::splat(0.0), f64x2::splat(EPSILON64) }
    #[cfg(feature="simd_support")]
    test_f64! { f64x4_edge_cases, f64x4, f64x4::splat(0.0), f64x4::splat(EPSILON64) }
    #[cfg(feature="simd_support")]
    test_f64! { f64x8_edge_cases, f64x8, f64x8::splat(0.0), f64x8::splat(EPSILON64) }

    #[cfg(feature = "std")]
    #[test]
    fn test_highprecision() {
        let mut r = ::test::rng(601);

        macro_rules! float_test {
            ($ty:ty, $uty:ty, $ity:ty, $extra:expr, $test_vals:expr) => {
                // Create a closure to make loop labels local
                (|| {
                    let mut vals: Vec<$ty> =
                      $test_vals.iter().cloned()
                        .flat_map(|x| $extra.iter().map(move |y| x + y))
                        .map(|x| <$ty>::from_bits(x as $uty))
                        .flat_map(|x| vec![x, -x].into_iter())
                        .filter(|x| x.is_finite())
                        .collect();
                    vals.sort_by(|a, b| a.partial_cmp(b).unwrap());
                    vals.dedup();

                    for a in vals.iter().cloned() {
                        for b in vals.iter().cloned().filter(|&b| b > a) {
                            fn to_signed_bits(val: $ty) -> $ity {
                                if val >= 0.0 {
                                    val.to_bits() as $ity
                                } else {
                                    -((-val).to_bits() as $ity)
                                }
                            }
                            fn from_signed_bits(val: $ity) -> $ty {
                                if val >= 0 {
                                    <$ty>::from_bits(val as $uty)
                                } else {
                                    -<$ty>::from_bits(-val as $uty)
                                }
                            }

                            let hp = HighPrecision::new(a, b);
                            let a_bits = to_signed_bits(a);
                            let b_bits = to_signed_bits(b);

                            const N_RUNS: usize = 10;
                            const N_REPS_PER_RUN: usize = 1000;

                            if (b_bits.wrapping_sub(a_bits) as $uty) < 100 {
                                // If a and b are "close enough", we can verify the full distribution
                                let mut counts = Vec::<i32>::with_capacity((b_bits - a_bits) as usize);
                                counts.resize((b_bits - a_bits) as usize, 0);
                                'test_loop_exact: for test_run in 1..(N_RUNS+1) {
                                    for _ in 0..N_REPS_PER_RUN {
                                        let res = hp.sample(&mut r);
                                        counts[(to_signed_bits(res) - a_bits) as usize] += 1;
                                    }
                                    for (count, i) in counts.iter().zip(0 as $ity..) {
                                        let expected = (test_run * N_REPS_PER_RUN) as $ty *
                                                       ((from_signed_bits(a_bits + i + 1) -
                                                         from_signed_bits(a_bits + i)) / (b - a));
                                        let err = (*count as $ty - expected) / expected;
                                        if err.abs() > 0.2 {
                                            if test_run < N_RUNS {
                                                continue 'test_loop_exact;
                                            }
                                            panic!(format!("Failed {}-bit exact test: a: 0x{:x}, b: 0x{:x}, err: {:.2}",
                                                           ::core::mem::size_of::<$ty>() * 8,
                                                           a.to_bits(),
                                                           b.to_bits(),
                                                           err.abs()));
                                        }
                                    }
                                }
                            } else {
                                // Otherwise divide range into 10 sections
                                let step = if (b - a).is_finite() {
                                    (b - a) / 10.0
                                } else {
                                    b / 10.0 - a / 10.0
                                };
                                assert!(step.is_finite());
                                let mut counts = Vec::<i32>::with_capacity(10);
                                counts.resize(10, 0);

                                'test_loop_rough: for test_run in 1..(N_RUNS+1) {
                                    for _ in 0..N_REPS_PER_RUN {
                                        let res = hp.sample(&mut r);
                                        assert!(a <= res && res < b);
                                        let index = (res / step - a / step) as usize;
                                        counts[::core::cmp::min(index, 9)] += 1;
                                    }
                                    for count in &counts {
                                        let expected = (test_run * N_REPS_PER_RUN) as $ty / 10.0;
                                        let err = (*count as $ty - expected) / expected;
                                        if err.abs() > 0.2 {
                                            if test_run < N_RUNS {
                                                continue 'test_loop_rough;
                                            }
                                            panic!(format!("Failed {}-bit rough test: a: 0x{:x}, b: 0x{:x}, err: {:.2}",
                                                           ::core::mem::size_of::<$ty>() * 8,
                                                           a.to_bits(),
                                                           b.to_bits(),
                                                           err.abs()));
                                        }
                                    }
                                }
                            }
                        }
                    }
                })()
            }
        }

        const SLOW_TESTS: bool = false;
        if SLOW_TESTS {
            // These test cases are commented out since they
            // take too long to run.
            float_test!(f64, u64, i64,
                [-5, -1, 0, 1, 7],
                [0i64,
                 0x0000_0f00_0000_0000,
                 0x0001_0000_0000_0000,
                 0x0004_0000_0000_0000,
                 0x0008_0000_0000_0000,
                 0x0010_0000_0000_0000,
                 0x0020_0000_0000_0000,
                 0x0040_0000_0000_0000,
                 0x0100_0000_0000_0000,
                 0x00cd_ef12_3456_789a,
                 0x0100_ffff_ffff_ffff,
                 0x010f_ffff_ffff_ffff,
                 0x0400_1234_5678_abcd,
                 0x7fef_ffff_ffff_ffff,
                 ]);
            float_test!(f32, u32, i32,
                [-5, -1, 0, 1, 7],
                [0i32,
                 0x000f_0000,
                 0x0008_0000,
                 0x0020_0000,
                 0x0040_0000,
                 0x0080_0000,
                 0x0100_0000,
                 0x0200_0000,
                 0x0800_0000,
                 0x5678_abcd,
                 0x0807_ffff,
                 0x087f_ffff,
                 0x4012_3456,
                 0x7f7f_ffff,
                 ]);
        } else {
            float_test!(f64, u64, i64,
                [0],
                [0i64,
                 1,
                 0x0000_0f00_0000_0000,
                 0x0000_0f00_0000_0005,
                 0x000f_ffff_ffff_fffd,
                 0x0010_0000_0000_0000,
                 0x0040_0000_0000_0000,
                 0x0100_ffff_ffff_ffff,
                 0x0101_0000_0000_0004,
                 0x7fef_ffff_ffff_ffff,
                 ]);
            float_test!(f32, u32, i32,
                [0],
                [0i32,
                 1,
                 0x000f_0000,
                 0x000f_0005,
                 0x007f_fffd,
                 0x0080_0000,
                 0x0200_0000,
                 0x0807_ffff,
                 0x0808_0004,
                 0x7f7f_ffff,
                 ]);
        }
    }
}
