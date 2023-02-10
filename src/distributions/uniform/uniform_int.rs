// Copyright 2018-2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::{SampleBorrow, SampleUniform, UniformSampler};
use crate::distributions::utils::WideningMultiply;
use crate::Rng;
#[cfg(feature = "serde1")] use serde::{Deserialize, Serialize};

/// The back-end implementing [`UniformSampler`] for integer types.
///
/// Unless you are implementing [`UniformSampler`] for your own type, this type
/// should not be used directly, use [`Uniform`] instead.
///
/// # Implementation notes
///
/// For simplicity, we use the same generic struct `UniformInt<X>` for all
/// integer types `X`. This gives us only one field type, `X`; to store unsigned
/// values of this size, we take use the fact that these conversions are no-ops.
///
/// For a closed range, the number of possible numbers we should generate is
/// `range = (high - low + 1)`. To avoid bias, we must ensure that the size of
/// our sample space, `zone`, is a multiple of `range`; other values must be
/// rejected (by replacing with a new random sample).
///
/// As a special case, we use `range = 0` to represent the full range of the
/// result type (i.e. for `new_inclusive($ty::MIN, $ty::MAX)`).
///
/// The optimum `zone` is the largest product of `range` which fits in our
/// (unsigned) target type. We calculate this by calculating how many numbers we
/// must reject: `reject = (MAX + 1) % range = (MAX - range + 1) % range`. Any (large)
/// product of `range` will suffice, thus in `sample_single` we multiply by a
/// power of 2 via bit-shifting (faster but may cause more rejections).
///
/// The smallest integer PRNGs generate is `u32`. For 8- and 16-bit outputs we
/// use `u32` for our `zone` and samples (because it's not slower and because
/// it reduces the chance of having to reject a sample). In this case we cannot
/// store `zone` in the target type since it is too large, however we know
/// `ints_to_reject < range <= $uty::MAX`.
///
/// An alternative to using a modulus is widening multiply: After a widening
/// multiply by `range`, the result is in the high word. Then comparing the low
/// word against `zone` makes sure our distribution is uniform.
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
pub struct UniformInt<X> {
    low: X,
    range: X,
    #[cfg(feature = "unbiased")]
    thresh: X, // effectively 2.pow(max(64, uty_bits)) % range
}

macro_rules! uniform_int_impl {
    ($ty:ty, $uty:ident, $sample_ty:ident) => {
        impl SampleUniform for $ty {
            type Sampler = UniformInt<$ty>;
        }

        impl UniformSampler for UniformInt<$ty> {
            // We play free and fast with unsigned vs signed here
            // (when $ty is signed), but that's fine, since the
            // contract of this macro is for $ty and $uty to be
            // "bit-equal", so casting between them is a no-op.

            type X = $ty;

            #[inline] // if the range is constant, this helps LLVM to do the
                      // calculations at compile-time.
            fn new<B1, B2>(low_b: B1, high_b: B2) -> Self
            where
                B1: SampleBorrow<Self::X> + Sized,
                B2: SampleBorrow<Self::X> + Sized,
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                assert!(low < high, "Uniform::new called with `low >= high`");
                UniformSampler::new_inclusive(low, high - 1)
            }

            #[inline] // if the range is constant, this helps LLVM to do the
                      // calculations at compile-time.
            fn new_inclusive<B1, B2>(low_b: B1, high_b: B2) -> Self
            where
                B1: SampleBorrow<Self::X> + Sized,
                B2: SampleBorrow<Self::X> + Sized,
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                assert!(
                    low <= high,
                    "Uniform::new_inclusive called with `low > high`"
                );

                let range = high.wrapping_sub(low).wrapping_add(1) as $uty;
                #[cfg(feature = "unbiased")]
                let thresh = if range > 0 {
                    let range = $sample_ty::from(range);
                    (range.wrapping_neg() % range)
                } else {
                    0
                };

                UniformInt {
                    low,
                    range: range as $ty, // type: $uty
                    #[cfg(feature = "unbiased")]
                    thresh: thresh as $uty as $ty, // type: $sample_ty
                }
            }

            /// Sample from distribution, Canon's method, biased
            ///
            /// In the worst case, bias affects 1 in `2^n` samples where n is
            /// 56 (`i8`), 48 (`i16`), 96 (`i32`), 64 (`i64`), 128 (`i128`).
            #[cfg(not(feature = "unbiased"))]
            #[inline]
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
                let range = self.range as $uty as $sample_ty;
                if range == 0 {
                    return rng.gen();
                }

                let (mut result, lo) = rng.gen::<$sample_ty>().wmul(range);

                if lo > range.wrapping_neg() {
                    let (new_hi, _) = (rng.gen::<$sample_ty>()).wmul(range);
                    let is_overflow = lo.checked_add(new_hi).is_none();
                    result += is_overflow as $sample_ty;
                }

                self.low.wrapping_add(result as $ty)
            }

            /// Sample from distribution, Lemire's method, unbiased
            #[cfg(feature = "unbiased")]
            #[inline]
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
                let range = self.range as $uty as $sample_ty;
                if range == 0 {
                    return rng.gen();
                }

                let thresh = self.thresh as $uty as $sample_ty;
                let hi = loop {
                    let (hi, lo) = rng.gen::<$sample_ty>().wmul(range);
                    if lo >= thresh {
                        break hi;
                    }
                };
                self.low.wrapping_add(hi as $ty)
            }

            #[inline]
            fn sample_single<R: Rng + ?Sized, B1, B2>(low_b: B1, high_b: B2, rng: &mut R) -> Self::X
            where
                B1: SampleBorrow<Self::X> + Sized,
                B2: SampleBorrow<Self::X> + Sized,
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                assert!(low < high, "UniformSampler::sample_single: low >= high");
                Self::sample_single_inclusive(low, high - 1, rng)
            }

            /// Sample single value, Canon's method, biased
            ///
            /// In the worst case, bias affects 1 in `2^n` samples where n is
            /// 56 (`i8`), 48 (`i16`), 96 (`i32`), 64 (`i64`), 128 (`i128`).
            #[cfg(not(feature = "unbiased"))]
            #[inline]
            fn sample_single_inclusive<R: Rng + ?Sized, B1, B2>(
                low_b: B1, high_b: B2, rng: &mut R,
            ) -> Self::X
            where
                B1: SampleBorrow<Self::X> + Sized,
                B2: SampleBorrow<Self::X> + Sized,
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                assert!(
                    low <= high,
                    "UniformSampler::sample_single_inclusive: low > high"
                );
                let range = high.wrapping_sub(low).wrapping_add(1) as $uty as $sample_ty;
                if range == 0 {
                    // Range is MAX+1 (unrepresentable), so we need a special case
                    return rng.gen();
                }

                // generate a sample using a sensible integer type
                let (mut result, lo_order) = rng.gen::<$sample_ty>().wmul(range);

                // if the sample is biased...
                if lo_order > range.wrapping_neg() {
                    // ...generate a new sample with 64 more bits, enough that bias is undetectable
                    let (new_hi_order, _) = (rng.gen::<$sample_ty>()).wmul(range as $sample_ty);
                    // and adjust if needed
                    result +=
                        lo_order.checked_add(new_hi_order as $sample_ty).is_none() as $sample_ty;
                }

                low.wrapping_add(result as $ty)
            }

            /// Sample single value, Canon's method, unbiased
            #[cfg(feature = "unbiased")]
            #[inline]
            fn sample_single_inclusive<R: Rng + ?Sized, B1, B2>(
                low_b: B1, high_b: B2, rng: &mut R,
            ) -> Self::X
            where
                B1: SampleBorrow<$ty> + Sized,
                B2: SampleBorrow<$ty> + Sized,
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                assert!(
                    low <= high,
                    "UniformSampler::sample_single_inclusive: low > high"
                );
                let range = high.wrapping_sub(low).wrapping_add(1) as $uty as $sample_ty;
                if range == 0 {
                    // Range is MAX+1 (unrepresentable), so we need a special case
                    return rng.gen();
                }

                let (mut result, mut lo) = rng.gen::<$sample_ty>().wmul(range);

                while lo > range.wrapping_neg() {
                    let (new_hi, new_lo) = (rng.gen::<$sample_ty>()).wmul(range);
                    match lo.checked_add(new_hi) {
                        Some(x) if x < $sample_ty::MAX => {
                            // Anything less than MAX: last term is 0
                            break;
                        }
                        None => {
                            // Overflow: last term is 1
                            result += 1;
                            break;
                        }
                        _ => {
                            // Unlikely case: must check next sample
                            lo = new_lo;
                            continue;
                        }
                    }
                }

                low.wrapping_add(result as $ty)
            }
        }
    };
}
uniform_int_impl! { i8, u8, u32 }
uniform_int_impl! { i16, u16, u32 }
uniform_int_impl! { i32, u32, u64 }
uniform_int_impl! { i64, u64, u64 }
uniform_int_impl! { i128, u128, u128 }
uniform_int_impl! { u8, u8, u32 }
uniform_int_impl! { u16, u16, u32}
uniform_int_impl! { u32, u32, u64 }
uniform_int_impl! { u64, u64, u64 }
uniform_int_impl! { u128, u128, u128 }
mod isize_int_impls {
    use super::*;
    uniform_int_impl! { isize, usize, usize }
    uniform_int_impl! { usize, usize, usize }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::distributions::uniform::{tests::test_samples, Uniform};

    #[test]
    #[cfg(feature = "serde1")]
    fn test_uniform_serialization() {
        let unit_box: Uniform<i32> = Uniform::new(-1, 1);
        let de_unit_box: Uniform<i32> =
            bincode::deserialize(&bincode::serialize(&unit_box).unwrap()).unwrap();

        assert_eq!(unit_box.0.low, de_unit_box.0.low);
        assert_eq!(unit_box.0.range, de_unit_box.0.range);
        assert_eq!(unit_box.0.z, de_unit_box.0.z);
    }

    #[should_panic]
    #[test]
    fn test_uniform_bad_limits_equal_int() {
        Uniform::new(10, 10);
    }

    #[test]
    fn test_uniform_good_limits_equal_int() {
        let mut rng = crate::test::rng(804);
        let dist = Uniform::new_inclusive(10, 10);
        for _ in 0..20 {
            assert_eq!(rng.sample(dist), 10);
        }
    }

    #[should_panic]
    #[test]
    fn test_uniform_bad_limits_flipped_int() {
        Uniform::new(10, 5);
    }

    #[test]
    #[cfg_attr(miri, ignore)] // Miri is too slow
    fn test_integers() {
        use core::{i128, u128};
        use core::{i16, i32, i64, i8, isize};
        use core::{u16, u32, u64, u8, usize};

        let mut rng = crate::test::rng(251);
        macro_rules! t {
            ($ty:ident, $v:expr, $le:expr, $lt:expr) => {{
                for &(low, high) in $v.iter() {
                    let my_uniform = Uniform::new(low, high);
                    for _ in 0..1000 {
                        let v: $ty = rng.sample(my_uniform);
                        assert!($le(low, v) && $lt(v, high));
                    }

                    let my_uniform = Uniform::new_inclusive(low, high);
                    for _ in 0..1000 {
                        let v: $ty = rng.sample(my_uniform);
                        assert!($le(low, v) && $le(v, high));
                    }

                    let my_uniform = Uniform::new(&low, high);
                    for _ in 0..1000 {
                        let v: $ty = rng.sample(my_uniform);
                        assert!($le(low, v) && $lt(v, high));
                    }

                    let my_uniform = Uniform::new_inclusive(&low, &high);
                    for _ in 0..1000 {
                        let v: $ty = rng.sample(my_uniform);
                        assert!($le(low, v) && $le(v, high));
                    }

                    for _ in 0..1000 {
                        let v = <$ty as SampleUniform>::Sampler::sample_single(low, high, &mut rng);
                        assert!($le(low, v) && $lt(v, high));
                    }

                    for _ in 0..1000 {
                        let v = <$ty as SampleUniform>::Sampler::sample_single_inclusive(low, high, &mut rng);
                        assert!($le(low, v) && $le(v, high));
                    }
                }
            }};

            // scalar bulk
            ($($ty:ident),*) => {{
                $(t!(
                    $ty,
                    [(0, 10), (10, 127), ($ty::MIN, $ty::MAX)],
                    |x, y| x <= y,
                    |x, y| x < y
                );)*
            }};
        }
        t!(i8, i16, i32, i64, isize, u8, u16, u32, u64, usize, i128, u128);
    }

    #[test]
    fn test_uniform_from_std_range() {
        let r = Uniform::from(2u32..7);
        assert_eq!(r.0.low, 2);
        assert_eq!(r.0.range, 5);
    }

    #[test]
    fn test_uniform_from_std_range_inclusive() {
        let r = Uniform::from(2u32..=6);
        assert_eq!(r.0.low, 2);
        assert_eq!(r.0.range, 5);
    }

    #[test]
    fn value_stability() {
        // We test on a sub-set of types; possibly we should do more.
        // TODO: SIMD types

        test_samples(11u8, 219, &[17, 66, 214], &[181, 93, 165]);
        test_samples(11u32, 219, &[17, 66, 214], &[181, 93, 165]);

        test_samples(0f32, 1e-2f32, &[0.0003070104, 0.0026630748, 0.00979833], &[
            0.008194133,
            0.00398172,
            0.007428536,
        ]);
        test_samples(
            -1e10f64,
            1e10f64,
            &[-4673848682.871551, 6388267422.932352, 4857075081.198343],
            &[1173375212.1808167, 1917642852.109581, 2365076174.3153973],
        );
    }

    #[test]
    fn uniform_distributions_can_be_compared() {
        assert_eq!(Uniform::new(1u32, 2u32), Uniform::new(1u32, 2u32));
    }
}
