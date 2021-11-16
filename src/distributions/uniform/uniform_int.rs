// Copyright 2018-2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::{SampleBorrow, SampleUniform, UniformSampler};
use crate::distributions::utils::WideningMultiply;
#[cfg(feature = "simd_support")]
use crate::distributions::utils::{OverflowingAdd, SimdCombine, SimdSplit};
use crate::Rng;
#[cfg(feature = "simd_support")] use packed_simd::*;
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
    low: X,
    range: X,
    nrmr: X, // range.wrapping_neg() % range
    z: X,    // either ints_to_reject or zone depending on implementation
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

                let (mut hi, mut lo) = rng.gen::<$u_large>().wmul(range);
                if lo < range {
                    while lo < (self.nrmr as $u_large) {
                        let (new_hi, new_lo) = rng.gen::<$u_large>().wmul(range);
                        hi = new_hi;
                        lo = new_lo;
                    }
                }
                self.low.wrapping_add(hi as $ty)
            }

            /// Sample, Canon's method
            #[inline]
            pub fn sample_canon<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                let range = self.range as $unsigned as $u_extra_large;
                if range == 0 {
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

                self.low.wrapping_add(result as $ty)
            }

            /// Sample, Canon's method with Lemire's early-out
            #[inline]
            pub fn sample_canon_lemire<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                let range = self.range as $unsigned as $u_extra_large;
                if range == 0 {
                    return rng.gen();
                }

                // generate a sample using a sensible integer type
                let (mut result, lo_order) = rng.gen::<$u_extra_large>().wmul(range);

                // if the sample is biased...
                if lo_order < (self.nrmr as $u_extra_large) {
                    // ...generate a new sample with 64 more bits, enough that bias is undetectable
                    let (new_hi_order, _) =
                        (rng.gen::<$u_extra_large>()).wmul(range as $u_extra_large);
                    // and adjust if needed
                    result += lo_order
                        .checked_add(new_hi_order as $u_extra_large)
                        .is_none() as $u_extra_large;
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
    }
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
    }
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

#[cfg(feature = "simd_support")]
macro_rules! uniform_simd_int_impl {
    ($ty:ident, $unsigned:ident, $u_scalar:ident) => {
        // The "pick the largest zone that can fit in an `u32`" optimization
        // is less useful here. Multiple lanes complicate things, we don't
        // know the PRNG's minimal output size, and casting to a larger vector
        // is generally a bad idea for SIMD performance. The user can still
        // implement it manually.

        // TODO: look into `Uniform::<u32x4>::new(0u32, 100)` functionality
        //       perhaps `impl SampleUniform for $u_scalar`?
        impl SampleUniform for $ty {
            type Sampler = UniformInt<$ty>;
        }

        impl UniformSampler for UniformInt<$ty> {
            type X = $ty;

            #[inline] // if the range is constant, this helps LLVM to do the
                      // calculations at compile-time.
            fn new<B1, B2>(low_b: B1, high_b: B2) -> Self
                where B1: SampleBorrow<Self::X> + Sized,
                      B2: SampleBorrow<Self::X> + Sized
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                assert!(low.lt(high).all(), "Uniform::new called with `low >= high`");
                UniformSampler::new_inclusive(low, high - 1)
            }

            #[inline] // if the range is constant, this helps LLVM to do the
                      // calculations at compile-time.
            fn new_inclusive<B1, B2>(low_b: B1, high_b: B2) -> Self
                where B1: SampleBorrow<Self::X> + Sized,
                      B2: SampleBorrow<Self::X> + Sized
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                assert!(low.le(high).all(),
                        "Uniform::new_inclusive called with `low > high`");
                let unsigned_max = ::core::$u_scalar::MAX;

                // NOTE: these may need to be replaced with explicitly
                // wrapping operations if `packed_simd` changes
                let range: $unsigned = ((high - low) + 1).cast();
                // `% 0` will panic at runtime.
                let not_full_range = range.gt($unsigned::splat(0));
                // replacing 0 with `unsigned_max` allows a faster `select`
                // with bitwise OR
                let modulo = not_full_range.select(range, $unsigned::splat(unsigned_max));
                // wrapping addition
                let ints_to_reject = (unsigned_max - range + 1) % modulo;
                // When `range` is 0, `lo` of `v.wmul(range)` will always be
                // zero which means only one sample is needed.
                let zone = unsigned_max - ints_to_reject;

                UniformInt {
                    low,
                    // These are really $unsigned values, but store as $ty:
                    range: range.cast(),
                    nrmr: ((0 - range) % range).cast(),
                    z: zone.cast(),
                }
            }

            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
                let range: $unsigned = self.range.cast();
                let zone: $unsigned = self.z.cast();

                // This might seem very slow, generating a whole new
                // SIMD vector for every sample rejection. For most uses
                // though, the chance of rejection is small and provides good
                // general performance. With multiple lanes, that chance is
                // multiplied. To mitigate this, we replace only the lanes of
                // the vector which fail, iteratively reducing the chance of
                // rejection. The replacement method does however add a little
                // overhead. Benchmarking or calculating probabilities might
                // reveal contexts where this replacement method is slower.
                let mut v: $unsigned = rng.gen();
                loop {
                    let (hi, lo) = v.wmul(range);
                    let mask = lo.le(zone);
                    if mask.all() {
                        let hi: $ty = hi.cast();
                        // wrapping addition
                        let result = self.low + hi;
                        // `select` here compiles to a blend operation
                        // When `range.eq(0).none()` the compare and blend
                        // operations are avoided.
                        let v: $ty = v.cast();
                        return range.gt($unsigned::splat(0)).select(result, v);
                    }
                    // Replace only the failing lanes
                    v = mask.select(v, rng.gen());
                }
            }
        }

        impl UniformInt<$ty> {
            /// Sample, Bitmask method
            #[inline]
            pub fn sample_bitmask<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                let mut range: $unsigned = self.range.cast();
                let is_full_range = range.eq($unsigned::splat(0));

                // the old impl use a mix of methods for different integer sizes, we only use
                // the lz method here for a better comparison.

                // generate bitmask
                range -= 1;
                let mut mask = range | 1;

                mask |= mask >> 1;
                mask |= mask >> 2;
                mask |= mask >> 4;

                const LANE_WIDTH: usize = std::mem::size_of::<$ty>() * 8 / <$ty>::lanes();
                if LANE_WIDTH >=  16 { mask |= mask >>  8; }
                if LANE_WIDTH >=  32 { mask |= mask >> 16; }
                if LANE_WIDTH >=  64 { mask |= mask >> 32; }
                if LANE_WIDTH >= 128 { mask |= mask >> 64; }

                let mut v: $unsigned = rng.gen();
                loop {
                    let masked = v & mask;
                    let accept = masked.le(range);
                    if accept.all() {
                        let masked: $ty = masked.cast();
                        // wrapping addition
                        let result = self.low + masked;
                        // `select` here compiles to a blend operation
                        // When `range.eq(0).none()` the compare and blend
                        // operations are avoided.
                        let v: $ty = v.cast();
                        return is_full_range.select(v, result);
                    }
                    // Replace only the failing lanes
                    v = accept.select(v, rng.gen());
                }
            }

            #[inline(always)]
            fn sample_inc_setup<B1, B2>(low_b: B1, high_b: B2) -> ($unsigned, $ty)
            where
                B1: SampleBorrow<$ty> + Sized,
                B2: SampleBorrow<$ty> + Sized,
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                assert!(low.le(high).all(), "UniformSampler::sample_single_inclusive: low > high");
                // wrapping sub and add
                let range: $unsigned = ((high - low) + 1).cast();
                (range, low)
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
                let (mut range, low) = Self::sample_inc_setup(low_b, high_b);
                let is_full_range = range.eq($unsigned::splat(0));

                // generate bitmask
                range -= 1;
                let mut mask = range | 1;

                mask |= mask >> 1;
                mask |= mask >> 2;
                mask |= mask >> 4;

                const LANE_WIDTH: usize = std::mem::size_of::<$ty>() * 8 / <$ty>::lanes();
                if LANE_WIDTH >=  16 { mask |= mask >>  8; }
                if LANE_WIDTH >=  32 { mask |= mask >> 16; }
                if LANE_WIDTH >=  64 { mask |= mask >> 32; }
                if LANE_WIDTH >= 128 { mask |= mask >> 64; }

                let mut v: $unsigned = rng.gen();
                loop {
                    let masked = v & mask;
                    let accept = masked.le(range);
                    if accept.all() {
                        let masked: $ty = masked.cast();
                        // wrapping addition
                        let result = low + masked;
                        // `select` here compiles to a blend operation
                        // When `range.eq(0).none()` the compare and blend
                        // operations are avoided.
                        let v: $ty = v.cast();
                        return is_full_range.select(v, result);
                    }
                    // Replace only the failing lanes
                    v = accept.select(v, rng.gen());
                }
            }
        }
    };

    // bulk implementation
    ($(($unsigned:ident, $signed:ident),)+ $u_scalar:ident) => {
        $(
            uniform_simd_int_impl!($unsigned, $unsigned, $u_scalar);
            uniform_simd_int_impl!($signed, $unsigned, $u_scalar);
        )+
    };
}
/*
#[cfg(feature = "simd_support")]
macro_rules! uniform_simd_int_gt8_impl {
    ($ty:ident, $unsigned:ident) => {
        impl UniformInt<$ty> {
            #[inline(always)]
            fn canon_successive<R: Rng + ?Sized>(
                range: $unsigned,
                result: &mut $unsigned,
                lo_order: $unsigned,
                rng: &mut R
            ) {
                let mut vecs_64 = range.simd_split();
                for x in &mut vecs_64 {
                    *x = rng.gen::<u64x8>().wmul((*x).cast()).0.cast();
                }
                let cast_new_hi: $unsigned = vecs_64.simd_combine();

                let (_, overflowed) = lo_order.overflowing_add(cast_new_hi);
                *result += overflowed.select($unsigned::splat(1), $unsigned::splat(0));
            }
/*
            /// Canon's method
            #[inline(always)]
            pub fn sample_single_inclusive_canon_branchless<R: Rng + ?Sized, B1, B2>(
                low_b: B1, high_b: B2, rng: &mut R,
            ) -> $ty
            where
                B1: SampleBorrow<$ty> + Sized,
                B2: SampleBorrow<$ty> + Sized,
            {
                let (range, low) = Self::sample_inc_setup(low_b, high_b);
                let is_full_range = range.eq($unsigned::splat(0));

                let rand_bits = rng.gen::<$unsigned>();
                let (mut result, lo_order) = rand_bits.wmul(range);

                Self::canon_successive(range, &mut result, lo_order, rng);

                let cast_result: $ty = result.cast();
                let cast_rand_bits: $ty = rand_bits.cast();
                is_full_range.select(cast_rand_bits, low + cast_result)
            }

            ///
            #[inline(always)]
            pub fn sample_inclusive_canon_scalar<R: Rng + ?Sized, B1, B2>(
                _low_b: B1, _high_b: B2, _rng: &mut R,
            ) -> $ty
            where
                B1: SampleBorrow<$ty> + Sized,
                B2: SampleBorrow<$ty> + Sized,
            {
                Default::default() // dummy impl
            }

            /// Canon's method
            #[inline(always)]
            pub fn sample_single_inclusive_canon<R: Rng + ?Sized, B1, B2>(
                low_b: B1, high_b: B2, rng: &mut R,
            ) -> $ty
            where
                B1: SampleBorrow<$ty> + Sized,
                B2: SampleBorrow<$ty> + Sized,
            {
                let (range, low) = Self::sample_inc_setup(low_b, high_b);
                let is_full_range = range.eq($unsigned::splat(0));

                // generate a sample using a sensible integer type
                let rand_bits = rng.gen::<$unsigned>();
                let (mut result, lo_order) = rand_bits.wmul(range);

                if lo_order.gt(0 - range).any() {
                    Self::canon_successive(range, &mut result, lo_order, rng);
                }

                let cast_result: $ty = result.cast();
                let cast_rand_bits: $ty = rand_bits.cast();
                is_full_range.select(cast_rand_bits, low + cast_result)
            }
*/
        }
    };

    ($(($unsigned:ident, $signed:ident)),+) => {$(
        uniform_simd_int_gt8_impl!{ $unsigned, $unsigned }
        uniform_simd_int_gt8_impl!{ $signed, $unsigned }
    )+};
}
*/

// These are the naive ports of the above algorithms to SIMD.
// Caveat: supports only up to x8, and at x8 it relies on 512-bit SIMD.
// Caveat: always generates u64 samples which will often be missing.
#[cfg(feature = "simd_support")]
macro_rules! uniform_simd_int_le8_impl {
    ($ty:ident, $unsigned:ident, $u_extra_large:ident) => {
        impl UniformInt<$ty> {
            #[inline(always)]
            fn canon_successive<R: Rng + ?Sized>(
                range: $u_extra_large,
                result: &mut $u_extra_large,
                lo_order: $u_extra_large,
                rng: &mut R
            ) {
                // ...generate a new sample with 64 more bits, enough that bias is undetectable
                let new_bits: $u_extra_large = rng.gen::<$u_extra_large>();
                let (new_hi_order, _) = new_bits.wmul(range);
                // and adjust if needed
                let (_, overflowed) = lo_order.overflowing_add(new_hi_order);
                *result += overflowed.select($u_extra_large::splat(1), $u_extra_large::splat(0));
            }

            /// Sample, Canon's method
            #[inline]
            pub fn sample_canon<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                let range: $unsigned = self.range.cast();
                let is_full_range = range.eq($unsigned::splat(0));
                let range: $u_extra_large = range.cast();

                // generate a sample using a sensible integer type
                let rand_bits = rng.gen::<$u_extra_large>();
                let (mut result, lo_order) = rand_bits.wmul(range);

                if lo_order.gt(0 - range).any() {
                    Self::canon_successive(range, &mut result, lo_order, rng);
                }

                // truncate and return the result:
                let result: $ty = result.cast();
                let rand_bits: $ty = rand_bits.cast();
                is_full_range.select(rand_bits, self.low + result)
            }

            /// Sample, Canon's method with Lemire's early-out
            #[inline]
            pub fn sample_canon_lemire<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                let range: $unsigned = self.range.cast();
                let is_full_range = range.eq($unsigned::splat(0));
                let range: $u_extra_large = range.cast();

                // generate a sample using a sensible integer type
                let rand_bits = rng.gen::<$u_extra_large>();
                let (mut result, lo_order) = rand_bits.wmul(range);

                let nrmr: $unsigned = self.nrmr.cast();
                let nrmr: $u_extra_large = nrmr.cast();
                if lo_order.lt(nrmr).any() {
                    Self::canon_successive(range, &mut result, lo_order, rng);
                }

                // truncate and return the result:
                let result: $ty = result.cast();
                let rand_bits: $ty = rand_bits.cast();
                is_full_range.select(rand_bits, self.low + result)
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
                let (range, low) = Self::sample_inc_setup(low_b, high_b);
                let is_full_range = range.eq($unsigned::splat(0));
                let range: $u_extra_large = range.cast();

                // generate a sample using a sensible integer type
                let rand_bits = rng.gen::<$u_extra_large>();
                let (mut result, lo_order) = rand_bits.wmul(range);

                if lo_order.gt(0 - range).any() {
                    Self::canon_successive(range, &mut result, lo_order, rng);
                }

                // truncate and return the result:
                let result: $ty = result.cast();
                let rand_bits: $ty = rand_bits.cast();
                is_full_range.select(rand_bits, low + result)
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
                let (range, low) = Self::sample_inc_setup(low_b, high_b);
                let is_full_range = range.eq($unsigned::splat(0));
                let range: $u_extra_large = range.cast();

                // generate a sample using a sensible integer type
                let rand_bits = rng.gen::<$u_extra_large>();
                let (mut result, lo_order) = rand_bits.wmul(range);

                let nrmr = ((0 - range) % range);
                if lo_order.lt(nrmr).any() {
                    Self::canon_successive(range, &mut result, lo_order, rng);
                }

                // truncate and return the result:
                let result: $ty = result.cast();
                let rand_bits: $ty = rand_bits.cast();
                is_full_range.select(rand_bits, low + result)
            }
        }
    };

    ($(($unsigned:ident, $signed:ident, $u_extra_large:ident),)+) => {$(
        uniform_simd_int_le8_impl!{ $unsigned, $unsigned, $u_extra_large }
        uniform_simd_int_le8_impl!{ $signed, $unsigned, $u_extra_large }
    )+};
}

#[cfg(feature = "simd_support")]
uniform_simd_int_impl! {
    (u128x2, i128x2),
    (u128x4, i128x4),
    u128
}
// #[cfg(feature = "simd_support")]
// uniform_simd_int_impl! {
// (usizex2, isizex2),
// (usizex4, isizex4),
// (usizex8, isizex8),
// usize
// }
#[cfg(feature = "simd_support")]
uniform_simd_int_impl! {
    (u64x2, i64x2),
    (u64x4, i64x4),
    (u64x8, i64x8),
    u64
}
#[cfg(feature = "simd_support")]
uniform_simd_int_impl! {
    (u32x2, i32x2),
    (u32x4, i32x4),
    (u32x8, i32x8),
    (u32x16, i32x16),
    u32
}
#[cfg(feature = "simd_support")]
uniform_simd_int_impl! {
    (u16x2, i16x2),
    (u16x4, i16x4),
    (u16x8, i16x8),
    (u16x16, i16x16),
    (u16x32, i16x32),
    u16
}
#[cfg(feature = "simd_support")]
uniform_simd_int_impl! {
    (u8x2, i8x2),
    (u8x4, i8x4),
    (u8x8, i8x8),
    (u8x16, i8x16),
    (u8x32, i8x32),
    (u8x64, i8x64),
    u8
}

// #[cfg(feature = "simd_support")]
// uniform_simd_int_gt8_impl! {
//     (u8x16, i8x16),
//     (u8x32, i8x32),
//     (u8x64, i8x64),
//
//     (u16x16, i16x16),
//     (u16x32, i16x32),
//
//     (u32x16, i32x16)
// }
#[cfg(feature = "simd_support")]
uniform_simd_int_le8_impl! {
    (u8x2, i8x2, u64x2),
    (u8x4, i8x4, u64x4),
    (u8x8, i8x8, u64x8),

    (u16x2, i16x2, u64x2),
    (u16x4, i16x4, u64x4),
    (u16x8, i16x8, u64x8),

    (u32x2, i32x2, u64x2),
    (u32x4, i32x4, u64x4),
    (u32x8, i32x8, u64x8),

    (u64x2, i64x2, u64x2),
    (u64x4, i64x4, u64x4),
    (u64x8, i64x8, u64x8),

    (u128x2, i128x2, u128x2),
    (u128x4, i128x4, u128x4),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::distributions::uniform::tests::test_samples;
    use crate::distributions::Uniform;

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

            // simd bulk
            ($($ty:ident),* => $scalar:ident) => {{
                $(t!(
                    $ty,
                    [
                        ($ty::splat(0), $ty::splat(10)),
                        ($ty::splat(10), $ty::splat(127)),
                        ($ty::splat($scalar::MIN), $ty::splat($scalar::MAX)),
                    ],
                    |x: $ty, y| x.le(y).all(),
                    |x: $ty, y| x.lt(y).all()
                );)*
            }};
        }
        t!(i8, i16, i32, i64, isize, u8, u16, u32, u64, usize, i128, u128);

        #[cfg(feature = "simd_support")]
        {
            t!(u8x2, u8x4, u8x8, u8x16, u8x32, u8x64 => u8);
            t!(i8x2, i8x4, i8x8, i8x16, i8x32, i8x64 => i8);
            t!(u16x2, u16x4, u16x8, u16x16, u16x32 => u16);
            t!(i16x2, i16x4, i16x8, i16x16, i16x32 => i16);
            t!(u32x2, u32x4, u32x8, u32x16 => u32);
            t!(i32x2, i32x4, i32x8, i32x16 => i32);
            t!(u64x2, u64x4, u64x8 => u64);
            t!(i64x2, i64x4, i64x8 => i64);
        }
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
