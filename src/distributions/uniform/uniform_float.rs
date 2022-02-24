// Copyright 2018-2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::{SampleBorrow, SampleUniform, UniformSampler};
use crate::distributions::float::IntoFloat;
use crate::distributions::utils::{BoolAsSIMD, FloatAsSIMD, FloatSIMDUtils};
use crate::Rng;
#[cfg(feature = "simd_support")] use packed_simd::*;
#[cfg(feature = "serde1")] use serde::{Deserialize, Serialize};

/// The back-end implementing [`UniformSampler`] for floating-point types.
///
/// Unless you are implementing [`UniformSampler`] for your own type, this type
/// should not be used directly, use [`Uniform`] instead.
///
/// # Implementation notes
///
/// Instead of generating a float in the `[0, 1)` range using [`Standard`], the
/// `UniformFloat` implementation converts the output of an PRNG itself. This
/// way one or two steps can be optimized out.
///
/// The floats are first converted to a value in the `[1, 2)` interval using a
/// transmute-based method, and then mapped to the expected range with a
/// multiply and addition. Values produced this way have what equals 23 bits of
/// random digits for an `f32`, and 52 for an `f64`.
///
/// [`new`]: UniformSampler::new
/// [`new_inclusive`]: UniformSampler::new_inclusive
/// [`Standard`]: crate::distributions::Standard
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
pub struct UniformFloat<X> {
    low: X,
    scale: X,
}

macro_rules! uniform_float_impl {
    ($ty:ty, $uty:ident, $f_scalar:ident, $u_scalar:ident, $bits_to_discard:expr) => {
        impl SampleUniform for $ty {
            type Sampler = UniformFloat<$ty>;
        }

        impl UniformSampler for UniformFloat<$ty> {
            type X = $ty;

            fn new<B1, B2>(low_b: B1, high_b: B2) -> Self
            where
                B1: SampleBorrow<Self::X> + Sized,
                B2: SampleBorrow<Self::X> + Sized,
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                debug_assert!(
                    low.all_finite(),
                    "Uniform::new called with `low` non-finite."
                );
                debug_assert!(
                    high.all_finite(),
                    "Uniform::new called with `high` non-finite."
                );
                assert!(low.all_lt(high), "Uniform::new called with `low >= high`");
                let max_rand = <$ty>::splat(
                    (::core::$u_scalar::MAX >> $bits_to_discard).into_float_with_exponent(0) - 1.0,
                );

                let mut scale = high - low;
                assert!(scale.all_finite(), "Uniform::new: range overflow");

                loop {
                    let mask = (scale * max_rand + low).ge_mask(high);
                    if mask.none() {
                        break;
                    }
                    scale = scale.decrease_masked(mask);
                }

                debug_assert!(<$ty>::splat(0.0).all_le(scale));

                UniformFloat { low, scale }
            }

            fn new_inclusive<B1, B2>(low_b: B1, high_b: B2) -> Self
            where
                B1: SampleBorrow<Self::X> + Sized,
                B2: SampleBorrow<Self::X> + Sized,
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                debug_assert!(
                    low.all_finite(),
                    "Uniform::new_inclusive called with `low` non-finite."
                );
                debug_assert!(
                    high.all_finite(),
                    "Uniform::new_inclusive called with `high` non-finite."
                );
                assert!(
                    low.all_le(high),
                    "Uniform::new_inclusive called with `low > high`"
                );
                let max_rand = <$ty>::splat(
                    (::core::$u_scalar::MAX >> $bits_to_discard).into_float_with_exponent(0) - 1.0,
                );

                let mut scale = (high - low) / max_rand;
                assert!(scale.all_finite(), "Uniform::new_inclusive: range overflow");

                loop {
                    let mask = (scale * max_rand + low).gt_mask(high);
                    if mask.none() {
                        break;
                    }
                    scale = scale.decrease_masked(mask);
                }

                debug_assert!(<$ty>::splat(0.0).all_le(scale));

                UniformFloat { low, scale }
            }

            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
                // Generate a value in the range [1, 2)
                let value1_2 = (rng.gen::<$uty>() >> $bits_to_discard).into_float_with_exponent(0);

                // Get a value in the range [0, 1) in order to avoid
                // overflowing into infinity when multiplying with scale
                let value0_1 = value1_2 - 1.0;

                // We don't use `f64::mul_add`, because it is not available with
                // `no_std`. Furthermore, it is slower for some targets (but
                // faster for others). However, the order of multiplication and
                // addition is important, because on some platforms (e.g. ARM)
                // it will be optimized to a single (non-FMA) instruction.
                value0_1 * self.scale + self.low
            }

            #[inline]
            fn sample_single<R: Rng + ?Sized, B1, B2>(low_b: B1, high_b: B2, rng: &mut R) -> Self::X
            where
                B1: SampleBorrow<Self::X> + Sized,
                B2: SampleBorrow<Self::X> + Sized,
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                debug_assert!(
                    low.all_finite(),
                    "UniformSampler::sample_single called with `low` non-finite."
                );
                debug_assert!(
                    high.all_finite(),
                    "UniformSampler::sample_single called with `high` non-finite."
                );
                assert!(
                    low.all_lt(high),
                    "UniformSampler::sample_single: low >= high"
                );
                let mut scale = high - low;
                assert!(
                    scale.all_finite(),
                    "UniformSampler::sample_single: range overflow"
                );

                loop {
                    // Generate a value in the range [1, 2)
                    let value1_2 =
                        (rng.gen::<$uty>() >> $bits_to_discard).into_float_with_exponent(0);

                    // Get a value in the range [0, 1) in order to avoid
                    // overflowing into infinity when multiplying with scale
                    let value0_1 = value1_2 - 1.0;

                    // Doing multiply before addition allows some architectures
                    // to use a single instruction.
                    let res = value0_1 * scale + low;

                    debug_assert!(low.all_le(res) || !scale.all_finite());
                    if res.all_lt(high) {
                        return res;
                    }

                    // This handles a number of edge cases.
                    // * `low` or `high` is NaN. In this case `scale` and
                    //   `res` are going to end up as NaN.
                    // * `low` is negative infinity and `high` is finite.
                    //   `scale` is going to be infinite and `res` will be
                    //   NaN.
                    // * `high` is positive infinity and `low` is finite.
                    //   `scale` is going to be infinite and `res` will
                    //   be infinite or NaN (if value0_1 is 0).
                    // * `low` is negative infinity and `high` is positive
                    //   infinity. `scale` will be infinite and `res` will
                    //   be NaN.
                    // * `low` and `high` are finite, but `high - low`
                    //   overflows to infinite. `scale` will be infinite
                    //   and `res` will be infinite or NaN (if value0_1 is 0).
                    // So if `high` or `low` are non-finite, we are guaranteed
                    // to fail the `res < high` check above and end up here.
                    //
                    // While we technically should check for non-finite `low`
                    // and `high` before entering the loop, by doing the checks
                    // here instead, we allow the common case to avoid these
                    // checks. But we are still guaranteed that if `low` or
                    // `high` are non-finite we'll end up here and can do the
                    // appropriate checks.
                    //
                    // Likewise `high - low` overflowing to infinity is also
                    // rare, so handle it here after the common case.
                    let mask = !scale.finite_mask();
                    if mask.any() {
                        assert!(
                            low.all_finite() && high.all_finite(),
                            "Uniform::sample_single: low and high must be finite"
                        );
                        scale = scale.decrease_masked(mask);
                    }
                }
            }
        }
    };
}

uniform_float_impl! { f32, u32, f32, u32, 32 - 23 }
uniform_float_impl! { f64, u64, f64, u64, 64 - 52 }

#[cfg(feature = "simd_support")]
uniform_float_impl! { f32x2, u32x2, f32, u32, 32 - 23 }
#[cfg(feature = "simd_support")]
uniform_float_impl! { f32x4, u32x4, f32, u32, 32 - 23 }
#[cfg(feature = "simd_support")]
uniform_float_impl! { f32x8, u32x8, f32, u32, 32 - 23 }
#[cfg(feature = "simd_support")]
uniform_float_impl! { f32x16, u32x16, f32, u32, 32 - 23 }

#[cfg(feature = "simd_support")]
uniform_float_impl! { f64x2, u64x2, f64, u64, 64 - 52 }
#[cfg(feature = "simd_support")]
uniform_float_impl! { f64x4, u64x4, f64, u64, 64 - 52 }
#[cfg(feature = "simd_support")]
uniform_float_impl! { f64x8, u64x8, f64, u64, 64 - 52 }

#[cfg(test)]
mod tests {
    use super::*;
    use crate::distributions::uniform::tests::test_samples;
    use crate::distributions::Uniform;
    use crate::rngs::mock::StepRng;

    #[test]
    #[cfg(feature = "serde1")]
    fn test_uniform_serialization() {
        let unit_box: Uniform<f32> = Uniform::new(-1., 1.);
        let de_unit_box: Uniform<f32> =
            bincode::deserialize(&bincode::serialize(&unit_box).unwrap()).unwrap();

        assert_eq!(unit_box.0.low, de_unit_box.0.low);
        assert_eq!(unit_box.0.scale, de_unit_box.0.scale);
    }

    #[test]
    #[cfg_attr(miri, ignore)] // Miri is too slow
    fn test_floats() {
        let mut rng = crate::test::rng(252);
        let mut zero_rng = StepRng::new(0, 0);
        let mut max_rng = StepRng::new(0xffff_ffff_ffff_ffff, 0);
        macro_rules! t {
            ($ty:ty, $f_scalar:ident, $bits_shifted:expr) => {{
                let v: &[($f_scalar, $f_scalar)] = &[
                    (0.0, 100.0),
                    (-1e35, -1e25),
                    (1e-35, 1e-25),
                    (-1e35, 1e35),
                    (<$f_scalar>::from_bits(0), <$f_scalar>::from_bits(3)),
                    (-<$f_scalar>::from_bits(10), -<$f_scalar>::from_bits(1)),
                    (-<$f_scalar>::from_bits(5), 0.0),
                    (-<$f_scalar>::from_bits(7), -0.0),
                    (0.1 * ::core::$f_scalar::MAX, ::core::$f_scalar::MAX),
                    (-::core::$f_scalar::MAX * 0.2, ::core::$f_scalar::MAX * 0.7),
                ];
                for &(low_scalar, high_scalar) in v.iter() {
                    for lane in 0..<$ty>::lanes() {
                        let low = <$ty>::splat(0.0 as $f_scalar).replace(lane, low_scalar);
                        let high = <$ty>::splat(1.0 as $f_scalar).replace(lane, high_scalar);
                        let my_uniform = Uniform::new(low, high);
                        let my_incl_uniform = Uniform::new_inclusive(low, high);
                        for _ in 0..100 {
                            let v = rng.sample(my_uniform).extract(lane);
                            assert!(low_scalar <= v && v < high_scalar);
                            let v = rng.sample(my_incl_uniform).extract(lane);
                            assert!(low_scalar <= v && v <= high_scalar);
                            let v =
                                <$ty as SampleUniform>::Sampler::sample_single(low, high, &mut rng)
                                    .extract(lane);
                            assert!(low_scalar <= v && v < high_scalar);
                        }

                        assert_eq!(
                            rng.sample(Uniform::new_inclusive(low, low)).extract(lane),
                            low_scalar
                        );

                        assert_eq!(zero_rng.sample(my_uniform).extract(lane), low_scalar);
                        assert_eq!(zero_rng.sample(my_incl_uniform).extract(lane), low_scalar);
                        assert_eq!(
                            <$ty as SampleUniform>::Sampler::sample_single(
                                low,
                                high,
                                &mut zero_rng
                            )
                            .extract(lane),
                            low_scalar
                        );
                        assert!(max_rng.sample(my_uniform).extract(lane) < high_scalar);
                        assert!(max_rng.sample(my_incl_uniform).extract(lane) <= high_scalar);

                        // Don't run this test for really tiny differences between high and low
                        // since for those rounding might result in selecting high for a very
                        // long time.
                        if (high_scalar - low_scalar) > 0.0001 {
                            let mut lowering_max_rng = StepRng::new(
                                0xffff_ffff_ffff_ffff,
                                (-1i64 << $bits_shifted) as u64,
                            );
                            assert!(
                                <$ty as SampleUniform>::Sampler::sample_single(
                                    low,
                                    high,
                                    &mut lowering_max_rng
                                )
                                .extract(lane)
                                    < high_scalar
                            );
                        }
                    }
                }

                assert_eq!(
                    rng.sample(Uniform::new_inclusive(
                        ::core::$f_scalar::MAX,
                        ::core::$f_scalar::MAX
                    )),
                    ::core::$f_scalar::MAX
                );
                assert_eq!(
                    rng.sample(Uniform::new_inclusive(
                        -::core::$f_scalar::MAX,
                        -::core::$f_scalar::MAX
                    )),
                    -::core::$f_scalar::MAX
                );
            }};
        }

        t!(f32, f32, 32 - 23);
        t!(f64, f64, 64 - 52);
        #[cfg(feature = "simd_support")]
        {
            t!(f32x2, f32, 32 - 23);
            t!(f32x4, f32, 32 - 23);
            t!(f32x8, f32, 32 - 23);
            t!(f32x16, f32, 32 - 23);
            t!(f64x2, f64, 64 - 52);
            t!(f64x4, f64, 64 - 52);
            t!(f64x8, f64, 64 - 52);
        }
    }

    #[test]
    #[should_panic]
    fn test_float_overflow() {
        let _ = Uniform::from(::core::f64::MIN..::core::f64::MAX);
    }

    #[test]
    #[should_panic]
    fn test_float_overflow_single() {
        let mut rng = crate::test::rng(252);
        rng.gen_range(::core::f64::MIN..::core::f64::MAX);
    }

    #[test]
    #[cfg(all(
        feature = "std",
        not(target_arch = "wasm32"),
        not(target_arch = "asmjs")
    ))]
    fn test_float_assertions() {
        use super::SampleUniform;
        use std::panic::catch_unwind;
        fn range<T: SampleUniform>(low: T, high: T) {
            let mut rng = crate::test::rng(253);
            T::Sampler::sample_single(low, high, &mut rng);
        }

        macro_rules! t {
            ($ty:ident, $f_scalar:ident) => {{
                let v: &[($f_scalar, $f_scalar)] = &[
                    (::std::$f_scalar::NAN, 0.0),
                    (1.0, ::std::$f_scalar::NAN),
                    (::std::$f_scalar::NAN, ::std::$f_scalar::NAN),
                    (1.0, 0.5),
                    (::std::$f_scalar::MAX, -::std::$f_scalar::MAX),
                    (::std::$f_scalar::INFINITY, ::std::$f_scalar::INFINITY),
                    (
                        ::std::$f_scalar::NEG_INFINITY,
                        ::std::$f_scalar::NEG_INFINITY,
                    ),
                    (::std::$f_scalar::NEG_INFINITY, 5.0),
                    (5.0, ::std::$f_scalar::INFINITY),
                    (::std::$f_scalar::NAN, ::std::$f_scalar::INFINITY),
                    (::std::$f_scalar::NEG_INFINITY, ::std::$f_scalar::NAN),
                    (::std::$f_scalar::NEG_INFINITY, ::std::$f_scalar::INFINITY),
                ];
                for &(low_scalar, high_scalar) in v.iter() {
                    for lane in 0..<$ty>::lanes() {
                        let low = <$ty>::splat(0.0 as $f_scalar).replace(lane, low_scalar);
                        let high = <$ty>::splat(1.0 as $f_scalar).replace(lane, high_scalar);
                        assert!(catch_unwind(|| range(low, high)).is_err());
                        assert!(catch_unwind(|| Uniform::new(low, high)).is_err());
                        assert!(catch_unwind(|| Uniform::new_inclusive(low, high)).is_err());
                        assert!(catch_unwind(|| range(low, low)).is_err());
                        assert!(catch_unwind(|| Uniform::new(low, low)).is_err());
                    }
                }
            }};
        }

        t!(f32, f32);
        t!(f64, f64);
        #[cfg(feature = "simd_support")]
        {
            t!(f32x2, f32);
            t!(f32x4, f32);
            t!(f32x8, f32);
            t!(f32x16, f32);
            t!(f64x2, f64);
            t!(f64x4, f64);
            t!(f64x8, f64);
        }
    }

    #[test]
    fn test_uniform_from_std_range() {
        let r = Uniform::from(2.0f64..7.0);
        assert_eq!(r.0.low, 2.0);
        assert_eq!(r.0.scale, 5.0);
    }

    #[test]
    fn test_uniform_from_std_range_inclusive() {
        let r = Uniform::from(2.0f64..=7.0);
        assert_eq!(r.0.low, 2.0);
        assert!(r.0.scale > 5.0);
        assert!(r.0.scale < 5.0 + 1e-14);
    }

    #[test]
    fn value_stability() {
        test_samples(0f32, 1000000f32, &[30701.041, 266307.47, 979833.0], &[
            819413.3, 398172.03, 742853.6,
        ]);
        test_samples(
            -1f64,
            1f64,
            &[-0.4673848682871551, 0.6388267422932352, 0.4857075081198343],
            &[0.11733752121808161, 0.191764285210958, 0.2365076174315397],
        );

        // TODO: SIMD types
    }

    #[test]
    fn uniform_distributions_can_be_compared() {
        assert_eq!(Uniform::new(1.0, 2.0), Uniform::new(1.0, 2.0));
    }
}
