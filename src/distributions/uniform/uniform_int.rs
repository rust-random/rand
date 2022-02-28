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
/// `ints_to_reject < range <= $unsigned::MAX`.
///
/// An alternative to using a modulus is widening multiply: After a widening
/// multiply by `range`, the result is in the high word. Then comparing the low
/// word against `zone` makes sure our distribution is uniform.
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
pub struct UniformInt<X> {
    // HACK: fields are pub(crate)
    pub(crate) low: X,
    pub(crate) range: X,
    pub(crate) nrmr: X, // range.wrapping_neg() % range
    pub(crate) z: X,    // either ints_to_reject or zone depending on implementation
}

macro_rules! uniform_int_impl {
    ($ty:ty, $unsigned:ident, $u_large:ident, $u_extra_large:ident) => {
        impl SampleUniform for $ty {
            type Sampler = UniformInt<$ty>;
        }

        impl UniformSampler for UniformInt<$ty> {
            // We play free and fast with unsigned vs signed here
            // (when $ty is signed), but that's fine, since the
            // contract of this macro is for $ty and $unsigned to be
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
                let unsigned_max = ::core::$u_large::MAX;

                let range = high.wrapping_sub(low).wrapping_add(1) as $unsigned;
                let ints_to_reject = if range > 0 {
                    let range = $u_large::from(range);
                    (unsigned_max - range + 1) % range
                } else {
                    0
                };

                UniformInt {
                    low,
                    // These are really $unsigned values, but store as $ty:
                    range: range as $ty,
                    nrmr: (range.wrapping_neg() % range) as $ty,
                    z: ints_to_reject as $unsigned as $ty,
                }
            }

            #[inline]
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
                let range = self.range as $unsigned as $u_large;
                if range == 0 {
                    return rng.gen();
                }

                let unsigned_max = ::core::$u_large::MAX;
                let zone = unsigned_max - (self.z as $unsigned as $u_large);
                loop {
                    let v: $u_large = rng.gen();
                    let (hi, lo) = v.wmul(range);
                    if lo <= zone {
                        return self.low.wrapping_add(hi as $ty);
                    }
                }
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
                let range = high.wrapping_sub(low).wrapping_add(1) as $unsigned as $u_large;
                if range == 0 {
                    // Range is MAX+1 (unrepresentable), so we need a special case
                    return rng.gen();
                }

                let zone = if ::core::$unsigned::MAX <= ::core::u16::MAX as $unsigned {
                    // Using a modulus is faster than the approximation for
                    // i8 and i16. I suppose we trade the cost of one
                    // modulus for near-perfect branch prediction.
                    let unsigned_max: $u_large = ::core::$u_large::MAX;
                    let ints_to_reject = (unsigned_max - range + 1) % range;
                    unsigned_max - ints_to_reject
                } else {
                    // conservative but fast approximation. `- 1` is necessary to allow the
                    // same comparison without bias.
                    (range << range.leading_zeros()).wrapping_sub(1)
                };

                loop {
                    let v: $u_large = rng.gen();
                    let (hi, lo) = v.wmul(range);
                    if lo <= zone {
                        return low.wrapping_add(hi as $ty);
                    }
                }
            }
        }

        impl UniformInt<$ty> {
            /// Sample, Lemire's method
            #[inline]
            pub fn sample_lemire<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                let range = self.range as $unsigned as $u_large;
                if range == 0 {
                    return rng.gen();
                }

                let thresh = self.nrmr as $u_large;
                let hi = loop {
                    let (hi, lo) = rng.gen::<$u_large>().wmul(range);
                    if lo >= thresh {
                        break hi;
                    }
                };
                self.low.wrapping_add(hi as $ty)
            }

            /// Sample, Canon's method, max(u64, $ty) samples, bias ≤ 1-in-2^(sample size)
            #[inline]
            pub fn sample_canon<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                let range = self.range as $unsigned as $u_extra_large;
                if range == 0 {
                    return rng.gen();
                }

                let (mut result, lo) = rng.gen::<$u_extra_large>().wmul(range);

                if lo > range.wrapping_neg() {
                    let (new_hi, _) = (rng.gen::<$u_extra_large>()).wmul(range);
                    let is_overflow = lo.checked_add(new_hi).is_none();
                    result += is_overflow as $u_extra_large;
                }

                self.low.wrapping_add(result as $ty)
            }

            /// Sample, Canon's method, max(u64, $ty) samples, unbiased
            #[inline]
            pub fn sample_canon_unbiased<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                let range = self.range as $unsigned as $u_extra_large;
                if range == 0 {
                    return rng.gen();
                }

                let (mut result, mut lo) = rng.gen::<$u_extra_large>().wmul(range);

                while lo > range.wrapping_neg() {
                    let (new_hi, new_lo) = (rng.gen::<$u_extra_large>()).wmul(range);
                    match lo.checked_add(new_hi) {
                        None => {
                            // Overflow: last term is 1
                            result += 1;
                            break;
                        }
                        Some(x) if x < $u_extra_large::MAX => {
                            // Anything less than MAX: last term is 0
                            break;
                        }
                        _ => {
                            // Unlikely case: must check next sample
                            lo = new_lo;
                            continue;
                        }
                    }
                }

                self.low.wrapping_add(result as $ty)
            }

            /// Sample, Canon's method with Lemire's early-out
            #[inline]
            pub fn sample_canon_lemire<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                let range = self.range as $unsigned as $u_extra_large;
                if range == 0 {
                    return rng.gen();
                }

                let (mut result, lo) = rng.gen::<$u_extra_large>().wmul(range);

                if lo < (self.nrmr as $u_extra_large) {
                    let (new_hi, _) = (rng.gen::<$u_extra_large>()).wmul(range);
                    let is_overflow = lo.checked_add(new_hi).is_none();
                    result += is_overflow as $u_extra_large;
                }

                self.low.wrapping_add(result as $ty)
            }

            /// Sample, Bitmask method
            #[inline]
            pub fn sample_bitmask<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                let mut range = self.range as $unsigned as $u_large;
                if range == 0 {
                    return rng.gen();
                }

                // the old impl use a mix of methods for different integer sizes, we only use
                // the lz method here for a better comparison.

                let mut mask = $u_large::max_value();
                range -= 1;
                mask >>= (range | 1).leading_zeros();
                loop {
                    let x = rng.gen::<$u_large>() & mask;
                    if x <= range {
                        return self.low.wrapping_add(x as $ty);
                    }
                }
            }

            /// Sample single inclusive, using ONeill's method
            #[inline]
            pub fn sample_single_inclusive_oneill<R: Rng + ?Sized, B1, B2>(
                low_b: B1, high_b: B2, rng: &mut R,
            ) -> $ty
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
                let range = high.wrapping_sub(low).wrapping_add(1) as $unsigned as $u_large;
                if range == 0 {
                    // Range is MAX+1 (unrepresentable), so we need a special case
                    return rng.gen();
                }

                // we use the "Debiased Int Mult (t-opt, m-opt)" rejection sampling method
                // described here https://www.pcg-random.org/posts/bounded-rands.html
                // and here https://github.com/imneme/bounded-rands

                let (mut hi, mut lo) = rng.gen::<$u_large>().wmul(range);
                if lo < range {
                    let mut threshold = range.wrapping_neg();
                    // this shortcut works best with large ranges
                    if threshold >= range {
                        threshold -= range;
                        if threshold >= range {
                            threshold %= range;
                        }
                    }
                    while lo < threshold {
                        let (new_hi, new_lo) = rng.gen::<$u_large>().wmul(range);
                        hi = new_hi;
                        lo = new_lo;
                    }
                }
                low.wrapping_add(hi as $ty)
            }

            /// Sample single inclusive, using Canon's method
            #[inline]
            pub fn sample_single_inclusive_canon<R: Rng + ?Sized, B1, B2>(
                low_b: B1, high_b: B2, rng: &mut R,
            ) -> $ty
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
                let range = high.wrapping_sub(low).wrapping_add(1) as $unsigned as $u_extra_large;
                if range == 0 {
                    // Range is MAX+1 (unrepresentable), so we need a special case
                    return rng.gen();
                }

                // generate a sample using a sensible integer type
                let (mut result, lo_order) = rng.gen::<$u_extra_large>().wmul(range);

                // if the sample is biased...
                if lo_order > range.wrapping_neg() {
                    // ...generate a new sample with 64 more bits, enough that bias is undetectable
                    let (new_hi_order, _) =
                        (rng.gen::<$u_extra_large>()).wmul(range as $u_extra_large);
                    // and adjust if needed
                    result += lo_order
                        .checked_add(new_hi_order as $u_extra_large)
                        .is_none() as $u_extra_large;
                }

                low.wrapping_add(result as $ty)
            }

            /// Sample, Canon's method, max(u64, $ty) samples, unbiased
            #[inline]
            pub fn sample_single_inclusive_canon_unbiased<R: Rng + ?Sized, B1, B2>(
                low_b: B1, high_b: B2, rng: &mut R,
            ) -> $ty
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
                let range = high.wrapping_sub(low).wrapping_add(1) as $unsigned as $u_extra_large;
                if range == 0 {
                    // Range is MAX+1 (unrepresentable), so we need a special case
                    return rng.gen();
                }

                let (mut result, mut lo) = rng.gen::<$u_extra_large>().wmul(range);

                while lo > range.wrapping_neg() {
                    let (new_hi, new_lo) = (rng.gen::<$u_extra_large>()).wmul(range);
                    match lo.checked_add(new_hi) {
                        None => {
                            // Overflow: last term is 1
                            result += 1;
                            break;
                        }
                        Some(x) if x < $u_extra_large::MAX => {
                            // Anything less than MAX: last term is 0
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

            /// Sample single inclusive, using Canon's method with Lemire's early-out
            #[inline]
            pub fn sample_inclusive_canon_lemire<R: Rng + ?Sized, B1, B2>(
                low_b: B1, high_b: B2, rng: &mut R,
            ) -> $ty
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
                let range = high.wrapping_sub(low).wrapping_add(1) as $unsigned as $u_extra_large;
                if range == 0 {
                    // Range is MAX+1 (unrepresentable), so we need a special case
                    return rng.gen();
                }

                // generate a sample using a sensible integer type
                let (mut result, lo_order) = rng.gen::<$u_extra_large>().wmul(range);

                // if the sample is biased... (since range won't be changing we can further
                // improve this check with a modulo)
                if lo_order < range.wrapping_neg() % range {
                    // ...generate a new sample with 64 more bits, enough that bias is undetectable
                    let (new_hi_order, _) =
                        (rng.gen::<$u_extra_large>()).wmul(range as $u_extra_large);
                    // and adjust if needed
                    result += lo_order
                        .checked_add(new_hi_order as $u_extra_large)
                        .is_none() as $u_extra_large;
                }

                low.wrapping_add(result as $ty)
            }

            /// Sample single inclusive, using the Bitmask method
            #[inline]
            pub fn sample_single_inclusive_bitmask<R: Rng + ?Sized, B1, B2>(
                low_b: B1, high_b: B2, rng: &mut R,
            ) -> $ty
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
                let mut range = high.wrapping_sub(low).wrapping_add(1) as $unsigned as $u_large;
                if range == 0 {
                    // Range is MAX+1 (unrepresentable), so we need a special case
                    return rng.gen();
                }

                // the old impl use a mix of methods for different integer sizes, we only use
                // the lz method here for a better comparison.

                let mut mask = $u_large::max_value();
                range -= 1;
                mask >>= (range | 1).leading_zeros();
                loop {
                    let x = rng.gen::<$u_large>() & mask;
                    if x <= range {
                        return low.wrapping_add(x as $ty);
                    }
                }
            }
        }
    };
}
uniform_int_impl! { i8, u8, u32, u64 }
uniform_int_impl! { i16, u16, u32, u64 }
uniform_int_impl! { i32, u32, u32, u64 }
uniform_int_impl! { i64, u64, u64, u64 }
uniform_int_impl! { i128, u128, u128, u128 }
uniform_int_impl! { u8, u8, u32, u64 }
uniform_int_impl! { u16, u16, u32, u64 }
uniform_int_impl! { u32, u32, u32, u64 }
uniform_int_impl! { u64, u64, u64, u64 }
uniform_int_impl! { u128, u128, u128, u128 }
#[cfg(any(target_pointer_width = "16", target_pointer_width = "32",))]
mod isize_int_impls {
    use super::*;
    uniform_int_impl! { isize, usize, usize, u64 }
    uniform_int_impl! { usize, usize, usize, u64 }
}
#[cfg(not(any(target_pointer_width = "16", target_pointer_width = "32",)))]
mod isize_int_impls {
    use super::*;
    uniform_int_impl! { isize, usize, usize, usize }
    uniform_int_impl! { usize, usize, usize, usize }
}

macro_rules! uniform_int_64_impl {
    ($ty:ty, $unsigned:ident) => {
        impl UniformInt<$ty> {
            /// Sample, Canon's method variant
            ///
            /// Variant: potential increase to bias (uses a single `u64` sample).
            #[inline]
            pub fn sample_canon_64<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                let range = self.range as $unsigned as u64;
                if range == 0 {
                    return rng.gen();
                }

                let (result, _lo1) = rng.gen::<u64>().wmul(range);
                // bias is at most 1 in 2.pow(56) for i8, 1 in 2.pow(48) for i16
                self.low.wrapping_add(result as $ty)
            }

            /// Sample single inclusive, using Canon's method variant
            ///
            /// Variant: potential increase to bias (uses a single `u64` sample).
            #[inline]
            pub fn sample_single_inclusive_canon_64<R: Rng + ?Sized, B1, B2>(
                low_b: B1, high_b: B2, rng: &mut R,
            ) -> $ty
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
                let range = high.wrapping_sub(low).wrapping_add(1) as $unsigned as u64;
                if range == 0 {
                    // Range is MAX+1 (unrepresentable), so we need a special case
                    return rng.gen();
                }

                // generate a sample using a sensible integer type
                let (result, _lo1) = rng.gen::<u64>().wmul(range);
                // bias is at most 1 in 2.pow(56) for i8, 1 in 2.pow(48) for i16
                low.wrapping_add(result as $ty)
            }
        }
    };
}
uniform_int_64_impl!(i8, u8);
uniform_int_64_impl!(i16, u16);

macro_rules! uniform_int_64void_impl {
    ($ty:ty) => {
        impl UniformInt<$ty> {
            /// Sample, Canon's method variant
            #[inline]
            pub fn sample_canon_64<R: Rng + ?Sized>(&self, _rng: &mut R) -> $ty {
                Default::default() // not used
            }

            /// Sample single inclusive, using Canon's method variant
            #[inline]
            pub fn sample_single_inclusive_canon_64<R: Rng + ?Sized, B1, B2>(
                _low_b: B1, _high_b: B2, _rng: &mut R,
            ) -> $ty
            where
                B1: SampleBorrow<$ty> + Sized,
                B2: SampleBorrow<$ty> + Sized,
            {
                Default::default() // not used
            }
        }
    };
}
uniform_int_64void_impl!(i32);
uniform_int_64void_impl!(i64);

impl UniformInt<i128> {
    /// Sample, Canon's method variant
    #[inline]
    pub fn sample_canon_64<R: Rng + ?Sized>(&self, rng: &mut R) -> i128 {
        let range = self.range as u128;
        if range == 0 {
            return rng.gen();
        }

        // Sample multiplied by 2.pow(-128) makes lo1 fractional (>>128):
        let (mut result, lo1) = rng.gen::<u128>().wmul(range);

        if lo1 > range.wrapping_neg() {
            // Generate more bits. Sample is multiplied by 2.pow(-192), so
            // hi2 is multiplied by 2.pow(-64):
            let (hi2, lo2) = (rng.gen::<u64>() as u128).wmul(range);
            debug_assert_eq!(hi2 >> 64, 0u128);
            let is_overflow = lo1.checked_add((hi2 << 64) | (lo2 >> 64)).is_none();
            result += is_overflow as u128;
        }

        self.low.wrapping_add(result as i128)
    }

    /// Sample single inclusive, using Canon's method variant
    ///
    /// Variant: potential increase to bias (uses a single `u64` sample).
    #[inline]
    pub fn sample_single_inclusive_canon_64<R: Rng + ?Sized, B1, B2>(
        low_b: B1, high_b: B2, rng: &mut R,
    ) -> i128
    where
        B1: SampleBorrow<i128> + Sized,
        B2: SampleBorrow<i128> + Sized,
    {
        let low = *low_b.borrow();
        let high = *high_b.borrow();
        assert!(
            low <= high,
            "UniformSampler::sample_single_inclusive: low > high"
        );
        let range = high.wrapping_sub(low).wrapping_add(1) as u128;
        if range == 0 {
            // Range is MAX+1 (unrepresentable), so we need a special case
            return rng.gen();
        }

        // generate a sample using a sensible integer type
        let (mut result, lo1) = rng.gen::<u128>().wmul(range);

        if lo1 > range.wrapping_neg() {
            // Generate more bits. Sample is multiplied by 2.pow(-192), so
            // hi2 is multiplied by 2.pow(-64):
            let (hi2, lo2) = (rng.gen::<u64>() as u128).wmul(range);
            debug_assert_eq!(hi2 >> 64, 0u128);
            let is_overflow = lo1.checked_add((hi2 << 64) | (lo2 >> 64)).is_none();
            result += is_overflow as u128;
        }

        low.wrapping_add(result as i128)
    }
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
