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
    // HACK: fields are pub(crate)
    pub(crate) low: X,
    pub(crate) range: X,
    pub(crate) thresh32_or_uty: X, // effectively 2.pow(max(32, uty_bits)) % range
    pub(crate) thresh64_or_uty: X, // effectively 2.pow(max(64, uty_bits)) % range
}

macro_rules! uniform_int_impl {
    ($ty:ty, $uty:ident, $u32_or_uty:ident, $u64_or_uty:ident) => {
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
                let (thresh32_or_uty, thresh64_or_uty);
                if range > 0 {
                    let range32 = $u32_or_uty::from(range);
                    thresh32_or_uty = (range32.wrapping_neg() % range32);

                    let range64 = $u64_or_uty::from(range);
                    thresh64_or_uty = (range64.wrapping_neg() % range64);
                } else {
                    thresh32_or_uty = 0;
                    thresh64_or_uty = 0;
                };

                UniformInt {
                    low,
                    range: range as $ty, // type: $uty
                    thresh32_or_uty: thresh32_or_uty as $uty as $ty, // type: $u32_or_uty
                    thresh64_or_uty: thresh64_or_uty as $uty as $ty, // type: $u64_or_uty
                }
            }

            #[inline]
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
                let range = self.range as $uty as $u32_or_uty;
                if range == 0 {
                    return rng.gen();
                }

                let unsigned_max = ::core::$u32_or_uty::MAX;
                let thresh = self.thresh32_or_uty as $uty as $u32_or_uty;
                let zone = unsigned_max - thresh;
                loop {
                    let v: $u32_or_uty = rng.gen();
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
                let range = high.wrapping_sub(low).wrapping_add(1) as $uty as $u32_or_uty;
                if range == 0 {
                    // Range is MAX+1 (unrepresentable), so we need a special case
                    return rng.gen();
                }

                let zone = if ::core::$uty::MAX <= ::core::u16::MAX as $uty {
                    // Using a modulus is faster than the approximation for
                    // i8 and i16. I suppose we trade the cost of one
                    // modulus for near-perfect branch prediction.
                    let unsigned_max: $u32_or_uty = ::core::$u32_or_uty::MAX;
                    let ints_to_reject = (unsigned_max - range + 1) % range;
                    unsigned_max - ints_to_reject
                } else {
                    // conservative but fast approximation. `- 1` is necessary to allow the
                    // same comparison without bias.
                    (range << range.leading_zeros()).wrapping_sub(1)
                };

                loop {
                    let v: $u32_or_uty = rng.gen();
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
                let range = self.range as $uty as $u64_or_uty;
                if range == 0 {
                    return rng.gen();
                }

                let thresh = self.thresh64_or_uty as $uty as $u64_or_uty;
                let hi = loop {
                    let (hi, lo) = rng.gen::<$u64_or_uty>().wmul(range);
                    if lo >= thresh {
                        break hi;
                    }
                };
                self.low.wrapping_add(hi as $ty)
            }

            /// Sample, Canon's method, max(u64, $ty) samples, bias ≤ 1-in-2^(sample size)
            #[inline]
            pub fn sample_canon<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                let range = self.range as $uty as $u64_or_uty;
                if range == 0 {
                    return rng.gen();
                }

                let (mut result, lo) = rng.gen::<$u64_or_uty>().wmul(range);

                if lo > range.wrapping_neg() {
                    let (new_hi, _) = (rng.gen::<$u64_or_uty>()).wmul(range);
                    let is_overflow = lo.checked_add(new_hi).is_none();
                    result += is_overflow as $u64_or_uty;
                }

                self.low.wrapping_add(result as $ty)
            }

            /// Sample, Canon's method, max(u32, $ty) samples, bias ≤ 1-in-2^(sample size)
            #[inline]
            pub fn sample_canon_u32<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                let range = self.range as $uty as $u32_or_uty;
                if range == 0 {
                    return rng.gen();
                }

                let (mut result, lo) = rng.gen::<$u32_or_uty>().wmul(range);

                if lo > range.wrapping_neg() {
                    let (new_hi, _) = (rng.gen::<$u32_or_uty>()).wmul(range);
                    let is_overflow = lo.checked_add(new_hi).is_none();
                    result += is_overflow as $u32_or_uty;
                }

                self.low.wrapping_add(result as $ty)
            }

            /// Sample, Canon's method, max(u64, $ty) samples, unbiased
            #[inline]
            pub fn sample_canon_unbiased<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                let range = self.range as $uty as $u64_or_uty;
                if range == 0 {
                    return rng.gen();
                }

                let (mut result, mut lo) = rng.gen::<$u64_or_uty>().wmul(range);

                while lo > range.wrapping_neg() {
                    let (new_hi, new_lo) = (rng.gen::<$u64_or_uty>()).wmul(range);
                    match lo.checked_add(new_hi) {
                        Some(x) if x < $u64_or_uty::MAX => {
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

                self.low.wrapping_add(result as $ty)
            }

            /// Sample, Canon's method, max(u32, $ty) samples, unbiased
            #[inline]
            pub fn sample_canon_u32_unbiased<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                let range = self.range as $uty as $u32_or_uty;
                if range == 0 {
                    return rng.gen();
                }

                let (mut result, mut lo) = rng.gen::<$u32_or_uty>().wmul(range);

                while lo > range.wrapping_neg() {
                    let (new_hi, new_lo) = (rng.gen::<$u32_or_uty>()).wmul(range);
                    match lo.checked_add(new_hi) {
                        Some(x) if x < $u32_or_uty::MAX => {
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

                self.low.wrapping_add(result as $ty)
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
                let range = high.wrapping_sub(low).wrapping_add(1) as $uty as $u64_or_uty;
                if range == 0 {
                    // Range is MAX+1 (unrepresentable), so we need a special case
                    return rng.gen();
                }

                // generate a sample using a sensible integer type
                let (mut result, lo_order) = rng.gen::<$u64_or_uty>().wmul(range);

                // if the sample is biased...
                if lo_order > range.wrapping_neg() {
                    // ...generate a new sample with 64 more bits, enough that bias is undetectable
                    let (new_hi_order, _) = (rng.gen::<$u64_or_uty>()).wmul(range as $u64_or_uty);
                    // and adjust if needed
                    result +=
                        lo_order.checked_add(new_hi_order as $u64_or_uty).is_none() as $u64_or_uty;
                }

                low.wrapping_add(result as $ty)
            }

            /// Sample single inclusive, using Canon's method (u32 samples)
            #[inline]
            pub fn sample_single_inclusive_canon_u32<R: Rng + ?Sized, B1, B2>(
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
                let range = high.wrapping_sub(low).wrapping_add(1) as $uty as $u32_or_uty;
                if range == 0 {
                    // Range is MAX+1 (unrepresentable), so we need a special case
                    return rng.gen();
                }

                // generate a sample using a sensible integer type
                let (mut result, lo_order) = rng.gen::<$u32_or_uty>().wmul(range);

                // if the sample is biased...
                if lo_order > range.wrapping_neg() {
                    // ...generate a new sample with 64 more bits, enough that bias is undetectable
                    let (new_hi_order, _) = (rng.gen::<$u32_or_uty>()).wmul(range as $u32_or_uty);
                    // and adjust if needed
                    result +=
                        lo_order.checked_add(new_hi_order as $u32_or_uty).is_none() as $u32_or_uty;
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
                let range = high.wrapping_sub(low).wrapping_add(1) as $uty as $u64_or_uty;
                if range == 0 {
                    // Range is MAX+1 (unrepresentable), so we need a special case
                    return rng.gen();
                }

                let (mut result, mut lo) = rng.gen::<$u64_or_uty>().wmul(range);

                while lo > range.wrapping_neg() {
                    let (new_hi, new_lo) = (rng.gen::<$u64_or_uty>()).wmul(range);
                    match lo.checked_add(new_hi) {
                        Some(x) if x < $u64_or_uty::MAX => {
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

            /// Sample, Canon's method, max(u64, $ty) samples, unbiased
            #[inline]
            pub fn sample_single_inclusive_canon_u32_unbiased<R: Rng + ?Sized, B1, B2>(
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
                let range = high.wrapping_sub(low).wrapping_add(1) as $uty as $u32_or_uty;
                if range == 0 {
                    // Range is MAX+1 (unrepresentable), so we need a special case
                    return rng.gen();
                }

                let (mut result, mut lo) = rng.gen::<$u32_or_uty>().wmul(range);

                while lo > range.wrapping_neg() {
                    let (new_hi, new_lo) = (rng.gen::<$u32_or_uty>()).wmul(range);
                    match lo.checked_add(new_hi) {
                        Some(x) if x < $u32_or_uty::MAX => {
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
    uniform_int_impl! { isize, usize, u32, u64 }
    uniform_int_impl! { usize, usize, u32, u64 }
}
#[cfg(not(any(target_pointer_width = "16", target_pointer_width = "32",)))]
mod isize_int_impls {
    use super::*;
    uniform_int_impl! { isize, usize, usize, usize }
    uniform_int_impl! { usize, usize, usize, usize }
}

macro_rules! uniform_int_canon_reduced_impl {
    ($ty:ty, $uty:ident, $u_half:ty, $shift:expr) => {
        impl UniformInt<$ty> {
            /// Sample, Canon's method variant
            #[inline]
            pub fn sample_canon_reduced<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                let range = self.range as $uty;
                if range == 0 {
                    return rng.gen();
                }

                let (mut result, lo1) = rng.gen::<$uty>().wmul(range);

                if lo1 > range.wrapping_neg() {
                    // Generate more bits. For i128, sample is multiplied by 2.pow(-192), so
                    // hi2 is multiplied by 2.pow(-64):
                    // TODO: can optimise since upper half of LHS is zero
                    let (hi2, lo2) = (rng.gen::<$u_half>() as $uty).wmul(range);
                    debug_assert_eq!(hi2 >> $shift, 0 as $uty);
                    let is_overflow = lo1.checked_add((hi2 << $shift) | (lo2 >> $shift)).is_none();
                    result += is_overflow as $uty;
                }

                self.low.wrapping_add(result as $ty)
            }

            /// Sample, Canon's method variant
            #[inline]
            pub fn sample_canon_reduced_unbiased<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                let range = self.range as $uty;
                if range == 0 {
                    return rng.gen();
                }

                let (mut result, mut lo) = rng.gen::<$uty>().wmul(range);

                while lo > range.wrapping_neg() {
                    let (hi2, lo2) = (rng.gen::<$u_half>() as $uty).wmul(range);
                    debug_assert_eq!(hi2 >> $shift, 0 as $uty);
                    match lo.checked_add((hi2 << $shift) | (lo2 >> $shift)) {
                        Some(x) if x < (<$u_half>::MAX as $uty) => {
                            // Anything less than MAX: cannot overflow
                            break;
                        }
                        Some(x) => {
                            const LOWER: $u_half = !0;
                            lo = (x << $shift) | (lo2 & (LOWER as $uty));
                            continue;
                        }
                        None => {
                            // Overflow: last term is 1
                            result += 1;
                            break;
                        }
                    }
                }

                self.low.wrapping_add(result as $ty)
            }

            /// Sample single inclusive, using Canon's method variant
            #[inline]
            pub fn sample_single_inclusive_canon_reduced<R: Rng + ?Sized, B1, B2>(
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
                let range = high.wrapping_sub(low).wrapping_add(1) as $uty;
                if range == 0 {
                    // Range is MAX+1 (unrepresentable), so we need a special case
                    return rng.gen();
                }

                let (mut result, lo1) = rng.gen::<$uty>().wmul(range);

                if lo1 > range.wrapping_neg() {
                    // Generate more bits. For i128, sample is multiplied by 2.pow(-192), so
                    // hi2 is multiplied by 2.pow(-64):
                    let (hi2, lo2) = (rng.gen::<$u_half>() as $uty).wmul(range);
                    debug_assert_eq!(hi2 >> $shift, 0 as $uty);
                    let is_overflow = lo1.checked_add((hi2 << $shift) | (lo2 >> $shift)).is_none();
                    result += is_overflow as $uty;
                }

                low.wrapping_add(result as $ty)
            }

            /// Sample single inclusive, using Canon's method variant
            #[inline]
            pub fn sample_single_inclusive_canon_reduced_unbiased<R: Rng + ?Sized, B1, B2>(
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
                let range = high.wrapping_sub(low).wrapping_add(1) as $uty;
                if range == 0 {
                    // Range is MAX+1 (unrepresentable), so we need a special case
                    return rng.gen();
                }

                let (mut result, mut lo) = rng.gen::<$uty>().wmul(range);

                while lo > range.wrapping_neg() {
                    let (hi2, lo2) = (rng.gen::<$u_half>() as $uty).wmul(range);
                    debug_assert_eq!(hi2 >> $shift, 0 as $uty);
                    match lo.checked_add((hi2 << $shift) | (lo2 >> $shift)) {
                        Some(x) if x < (<$u_half>::MAX as $uty) => {
                            // Anything less than MAX: cannot overflow
                            break;
                        }
                        Some(x) => {
                            const LOWER: $u_half = !0;
                            lo = (x << $shift) | (lo2 & (LOWER as $uty));
                            continue;
                        }
                        None => {
                            // Overflow: last term is 1
                            result += 1;
                            break;
                        }
                    }
                }

                low.wrapping_add(result as $ty)
            }
        }
    };
}

uniform_int_canon_reduced_impl!(u64, u64, u32, 32);
uniform_int_canon_reduced_impl!(i64, u64, u32, 32);
uniform_int_canon_reduced_impl!(i128, u128, u64, 64);

macro_rules! uniform_int_canon_u32_2_impl {
    // Bits <= 32
    ($ty:ty, $uty:ident) => {
        impl UniformInt<$ty> {
            /// Sample, Canon's method variant
            #[inline]
            pub fn sample_canon_u32_2<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                let range = self.range as $uty as u32;
                if range == 0 {
                    return rng.gen();
                }

                let (mut result, lo1) = rng.gen::<u32>().wmul(range);

                if lo1 > range.wrapping_neg() {
                    // Generate more bits. Sample is multiplied by 2.pow(-64),
                    // so hi2 is multiplied by 2.pow(-32):
                    let (hi2, lo2) = rng.gen::<u32>().wmul(range);
                    if let Some(sum) = lo1.checked_add(hi2) {
                        // No overflow yet; try adding more bits
                        if sum == u32::MAX {
                            let (hi3, _) = rng.gen::<u32>().wmul(range);
                            let is_overflow = lo2.checked_add(hi3).is_none();
                            result += is_overflow as u32;
                        }
                    } else {
                        // Overflow: short path
                        result += 1;
                    }
                }

                self.low.wrapping_add(result as $ty)
            }

            /// Sample single inclusive, using Canon's method variant
            #[inline]
            pub fn sample_single_inclusive_canon_u32_2<R: Rng + ?Sized, B1, B2>(
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
                let range = high.wrapping_sub(low).wrapping_add(1) as $uty as u32;
                if range == 0 {
                    // Range is MAX+1 (unrepresentable), so we need a special case
                    return rng.gen();
                }

                let (mut result, lo1) = rng.gen::<u32>().wmul(range);

                if lo1 > range.wrapping_neg() {
                    // Generate more bits. Sample is multiplied by 2.pow(-64),
                    // so hi2 is multiplied by 2.pow(-32):
                    let (hi2, lo2) = rng.gen::<u32>().wmul(range);
                    if let Some(sum) = lo1.checked_add(hi2) {
                        // No overflow yet; try adding more bits
                        if sum == u32::MAX {
                            let (hi3, _) = rng.gen::<u32>().wmul(range);
                            let is_overflow = lo2.checked_add(hi3).is_none();
                            result += is_overflow as u32;
                        }
                    } else {
                        // Overflow: short path
                        result += 1;
                    }
                }

                low.wrapping_add(result as $ty)
            }
        }
    };
}

uniform_int_canon_u32_2_impl!(i8, u8);
uniform_int_canon_u32_2_impl!(i16, u16);
uniform_int_canon_u32_2_impl!(i32, u32);

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
