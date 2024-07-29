// Copyright 2018-2020 Developers of the Rand project.
// Copyright 2017 The Rust Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! `UniformInt` implementation

use super::{Error, SampleBorrow, SampleUniform, UniformSampler};
use crate::distr::utils::WideningMultiply;
#[cfg(feature = "simd_support")]
use crate::distr::{Distribution, Standard};
use crate::Rng;

#[cfg(feature = "simd_support")]
use core::simd::prelude::*;
#[cfg(feature = "simd_support")]
use core::simd::{LaneCount, SupportedLaneCount};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

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
///
/// [`Uniform`]: super::Uniform
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct UniformInt<X> {
    pub(super) low: X,
    pub(super) range: X,
    thresh: X, // effectively 2.pow(max(64, uty_bits)) % range
}

macro_rules! uniform_int_impl {
    ($ty:ty, $uty:ty, $sample_ty:ident) => {
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
            fn new<B1, B2>(low_b: B1, high_b: B2) -> Result<Self, Error>
            where
                B1: SampleBorrow<Self::X> + Sized,
                B2: SampleBorrow<Self::X> + Sized,
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                if !(low < high) {
                    return Err(Error::EmptyRange);
                }
                UniformSampler::new_inclusive(low, high - 1)
            }

            #[inline] // if the range is constant, this helps LLVM to do the
                      // calculations at compile-time.
            fn new_inclusive<B1, B2>(low_b: B1, high_b: B2) -> Result<Self, Error>
            where
                B1: SampleBorrow<Self::X> + Sized,
                B2: SampleBorrow<Self::X> + Sized,
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                if !(low <= high) {
                    return Err(Error::EmptyRange);
                }

                let range = high.wrapping_sub(low).wrapping_add(1) as $uty;
                let thresh = if range > 0 {
                    let range = $sample_ty::from(range);
                    (range.wrapping_neg() % range)
                } else {
                    0
                };

                Ok(UniformInt {
                    low,
                    range: range as $ty,           // type: $uty
                    thresh: thresh as $uty as $ty, // type: $sample_ty
                })
            }

            /// Sample from distribution, Lemire's method, unbiased
            #[inline]
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
                let range = self.range as $uty as $sample_ty;
                if range == 0 {
                    return rng.random();
                }

                let thresh = self.thresh as $uty as $sample_ty;
                let hi = loop {
                    let (hi, lo) = rng.random::<$sample_ty>().wmul(range);
                    if lo >= thresh {
                        break hi;
                    }
                };
                self.low.wrapping_add(hi as $ty)
            }

            #[inline]
            fn sample_single<R: Rng + ?Sized, B1, B2>(
                low_b: B1,
                high_b: B2,
                rng: &mut R,
            ) -> Result<Self::X, Error>
            where
                B1: SampleBorrow<Self::X> + Sized,
                B2: SampleBorrow<Self::X> + Sized,
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                if !(low < high) {
                    return Err(Error::EmptyRange);
                }
                Self::sample_single_inclusive(low, high - 1, rng)
            }

            /// Sample single value, Canon's method, biased
            ///
            /// In the worst case, bias affects 1 in `2^n` samples where n is
            /// 56 (`i8`), 48 (`i16`), 96 (`i32`), 64 (`i64`), 128 (`i128`).
            #[cfg(not(feature = "unbiased"))]
            #[inline]
            fn sample_single_inclusive<R: Rng + ?Sized, B1, B2>(
                low_b: B1,
                high_b: B2,
                rng: &mut R,
            ) -> Result<Self::X, Error>
            where
                B1: SampleBorrow<Self::X> + Sized,
                B2: SampleBorrow<Self::X> + Sized,
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                if !(low <= high) {
                    return Err(Error::EmptyRange);
                }
                let range = high.wrapping_sub(low).wrapping_add(1) as $uty as $sample_ty;
                if range == 0 {
                    // Range is MAX+1 (unrepresentable), so we need a special case
                    return Ok(rng.random());
                }

                // generate a sample using a sensible integer type
                let (mut result, lo_order) = rng.random::<$sample_ty>().wmul(range);

                // if the sample is biased...
                if lo_order > range.wrapping_neg() {
                    // ...generate a new sample to reduce bias...
                    let (new_hi_order, _) = (rng.random::<$sample_ty>()).wmul(range as $sample_ty);
                    // ... incrementing result on overflow
                    let is_overflow = lo_order.checked_add(new_hi_order as $sample_ty).is_none();
                    result += is_overflow as $sample_ty;
                }

                Ok(low.wrapping_add(result as $ty))
            }

            /// Sample single value, Canon's method, unbiased
            #[cfg(feature = "unbiased")]
            #[inline]
            fn sample_single_inclusive<R: Rng + ?Sized, B1, B2>(
                low_b: B1,
                high_b: B2,
                rng: &mut R,
            ) -> Result<Self::X, Error>
            where
                B1: SampleBorrow<$ty> + Sized,
                B2: SampleBorrow<$ty> + Sized,
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                if !(low <= high) {
                    return Err(Error::EmptyRange);
                }
                let range = high.wrapping_sub(low).wrapping_add(1) as $uty as $sample_ty;
                if range == 0 {
                    // Range is MAX+1 (unrepresentable), so we need a special case
                    return Ok(rng.random());
                }

                let (mut result, mut lo) = rng.random::<$sample_ty>().wmul(range);

                // In contrast to the biased sampler, we use a loop:
                while lo > range.wrapping_neg() {
                    let (new_hi, new_lo) = (rng.random::<$sample_ty>()).wmul(range);
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

                Ok(low.wrapping_add(result as $ty))
            }
        }
    };
}

uniform_int_impl! { i8, u8, u32 }
uniform_int_impl! { i16, u16, u32 }
uniform_int_impl! { i32, u32, u32 }
uniform_int_impl! { i64, u64, u64 }
uniform_int_impl! { i128, u128, u128 }
uniform_int_impl! { u8, u8, u32 }
uniform_int_impl! { u16, u16, u32 }
uniform_int_impl! { u32, u32, u32 }
uniform_int_impl! { u64, u64, u64 }
uniform_int_impl! { u128, u128, u128 }

#[cfg(feature = "simd_support")]
macro_rules! uniform_simd_int_impl {
    ($ty:ident, $unsigned:ident) => {
        // The "pick the largest zone that can fit in an `u32`" optimization
        // is less useful here. Multiple lanes complicate things, we don't
        // know the PRNG's minimal output size, and casting to a larger vector
        // is generally a bad idea for SIMD performance. The user can still
        // implement it manually.

        #[cfg(feature = "simd_support")]
        impl<const LANES: usize> SampleUniform for Simd<$ty, LANES>
        where
            LaneCount<LANES>: SupportedLaneCount,
            Simd<$unsigned, LANES>:
                WideningMultiply<Output = (Simd<$unsigned, LANES>, Simd<$unsigned, LANES>)>,
            Standard: Distribution<Simd<$unsigned, LANES>>,
        {
            type Sampler = UniformInt<Simd<$ty, LANES>>;
        }

        #[cfg(feature = "simd_support")]
        impl<const LANES: usize> UniformSampler for UniformInt<Simd<$ty, LANES>>
        where
            LaneCount<LANES>: SupportedLaneCount,
            Simd<$unsigned, LANES>:
                WideningMultiply<Output = (Simd<$unsigned, LANES>, Simd<$unsigned, LANES>)>,
            Standard: Distribution<Simd<$unsigned, LANES>>,
        {
            type X = Simd<$ty, LANES>;

            #[inline] // if the range is constant, this helps LLVM to do the
                      // calculations at compile-time.
            fn new<B1, B2>(low_b: B1, high_b: B2) -> Result<Self, Error>
                where B1: SampleBorrow<Self::X> + Sized,
                      B2: SampleBorrow<Self::X> + Sized
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                if !(low.simd_lt(high).all()) {
                    return Err(Error::EmptyRange);
                }
                UniformSampler::new_inclusive(low, high - Simd::splat(1))
            }

            #[inline] // if the range is constant, this helps LLVM to do the
                      // calculations at compile-time.
            fn new_inclusive<B1, B2>(low_b: B1, high_b: B2) -> Result<Self, Error>
                where B1: SampleBorrow<Self::X> + Sized,
                      B2: SampleBorrow<Self::X> + Sized
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                if !(low.simd_le(high).all()) {
                    return Err(Error::EmptyRange);
                }

                // NOTE: all `Simd` operations are inherently wrapping,
                //       see https://doc.rust-lang.org/std/simd/struct.Simd.html
                let range: Simd<$unsigned, LANES> = ((high - low) + Simd::splat(1)).cast();

                // We must avoid divide-by-zero by using 0 % 1 == 0.
                let not_full_range = range.simd_gt(Simd::splat(0));
                let modulo = not_full_range.select(range, Simd::splat(1));
                let ints_to_reject = range.wrapping_neg() % modulo;

                Ok(UniformInt {
                    low,
                    // These are really $unsigned values, but store as $ty:
                    range: range.cast(),
                    thresh: ints_to_reject.cast(),
                })
            }

            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
                let range: Simd<$unsigned, LANES> = self.range.cast();
                let thresh: Simd<$unsigned, LANES> = self.thresh.cast();

                // This might seem very slow, generating a whole new
                // SIMD vector for every sample rejection. For most uses
                // though, the chance of rejection is small and provides good
                // general performance. With multiple lanes, that chance is
                // multiplied. To mitigate this, we replace only the lanes of
                // the vector which fail, iteratively reducing the chance of
                // rejection. The replacement method does however add a little
                // overhead. Benchmarking or calculating probabilities might
                // reveal contexts where this replacement method is slower.
                let mut v: Simd<$unsigned, LANES> = rng.random();
                loop {
                    let (hi, lo) = v.wmul(range);
                    let mask = lo.simd_ge(thresh);
                    if mask.all() {
                        let hi: Simd<$ty, LANES> = hi.cast();
                        // wrapping addition
                        let result = self.low + hi;
                        // `select` here compiles to a blend operation
                        // When `range.eq(0).none()` the compare and blend
                        // operations are avoided.
                        let v: Simd<$ty, LANES> = v.cast();
                        return range.simd_gt(Simd::splat(0)).select(result, v);
                    }
                    // Replace only the failing lanes
                    v = mask.select(v, rng.random());
                }
            }
        }
    };

    // bulk implementation
    ($(($unsigned:ident, $signed:ident)),+) => {
        $(
            uniform_simd_int_impl!($unsigned, $unsigned);
            uniform_simd_int_impl!($signed, $unsigned);
        )+
    };
}

#[cfg(feature = "simd_support")]
uniform_simd_int_impl! { (u8, i8), (u16, i16), (u32, i32), (u64, i64) }

/// The back-end implementing [`UniformSampler`] for `usize`.
///
/// # Implementation notes
///
/// Sampling a `usize` value is usually used in relation to the length of an
/// array or other memory structure, thus it is reasonable to assume that the
/// vast majority of use-cases will have a maximum size under [`u32::MAX`].
/// In part to optimise for this use-case, but mostly to ensure that results
/// are portable across 32-bit and 64-bit architectures (as far as is possible),
/// this implementation will use 32-bit sampling when possible.
#[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UniformUsize(UniformUsizeImpl);

#[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
impl SampleUniform for usize {
    type Sampler = UniformUsize;
}

#[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UniformUsizeImpl {
    U32(UniformInt<u32>),
    #[cfg(target_pointer_width = "64")]
    U64(UniformInt<u64>),
}

#[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
impl UniformSampler for UniformUsize {
    type X = usize;

    #[inline] // if the range is constant, this helps LLVM to do the
              // calculations at compile-time.
    fn new<B1, B2>(low_b: B1, high_b: B2) -> Result<Self, Error>
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let low = *low_b.borrow();
        let high = *high_b.borrow();
        if !(low < high) {
            return Err(Error::EmptyRange);
        }

        #[cfg(target_pointer_width = "64")]
        if high > (u32::MAX as usize) {
            return UniformInt::new(low as u64, high as u64)
                .map(|ui| UniformUsize(UniformUsizeImpl::U64(ui)));
        }

        UniformInt::new(low as u32, high as u32).map(|ui| UniformUsize(UniformUsizeImpl::U32(ui)))
    }

    #[inline] // if the range is constant, this helps LLVM to do the
              // calculations at compile-time.
    fn new_inclusive<B1, B2>(low_b: B1, high_b: B2) -> Result<Self, Error>
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let low = *low_b.borrow();
        let high = *high_b.borrow();
        if !(low <= high) {
            return Err(Error::EmptyRange);
        }

        #[cfg(target_pointer_width = "64")]
        if high > (u32::MAX as usize) {
            return UniformInt::new_inclusive(low as u64, high as u64)
                .map(|ui| UniformUsize(UniformUsizeImpl::U64(ui)));
        }

        UniformInt::new_inclusive(low as u32, high as u32)
            .map(|ui| UniformUsize(UniformUsizeImpl::U32(ui)))
    }

    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> usize {
        match self.0 {
            UniformUsizeImpl::U32(uu) => uu.sample(rng) as usize,
            #[cfg(target_pointer_width = "64")]
            UniformUsizeImpl::U64(uu) => uu.sample(rng) as usize,
        }
    }

    #[inline]
    fn sample_single<R: Rng + ?Sized, B1, B2>(
        low_b: B1,
        high_b: B2,
        rng: &mut R,
    ) -> Result<Self::X, Error>
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let low = *low_b.borrow();
        let high = *high_b.borrow();
        if !(low < high) {
            return Err(Error::EmptyRange);
        }

        #[cfg(target_pointer_width = "64")]
        if high > (u32::MAX as usize) {
            return UniformInt::<u64>::sample_single(low as u64, high as u64, rng)
                .map(|x| x as usize);
        }

        UniformInt::<u32>::sample_single(low as u32, high as u32, rng).map(|x| x as usize)
    }

    #[inline]
    fn sample_single_inclusive<R: Rng + ?Sized, B1, B2>(
        low_b: B1,
        high_b: B2,
        rng: &mut R,
    ) -> Result<Self::X, Error>
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let low = *low_b.borrow();
        let high = *high_b.borrow();
        if !(low <= high) {
            return Err(Error::EmptyRange);
        }

        #[cfg(target_pointer_width = "64")]
        if high > (u32::MAX as usize) {
            return UniformInt::<u64>::sample_single_inclusive(low as u64, high as u64, rng)
                .map(|x| x as usize);
        }

        UniformInt::<u32>::sample_single_inclusive(low as u32, high as u32, rng).map(|x| x as usize)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::distr::Uniform;

    #[test]
    fn test_uniform_bad_limits_equal_int() {
        assert_eq!(Uniform::new(10, 10), Err(Error::EmptyRange));
    }

    #[test]
    fn test_uniform_good_limits_equal_int() {
        let mut rng = crate::test::rng(804);
        let dist = Uniform::new_inclusive(10, 10).unwrap();
        for _ in 0..20 {
            assert_eq!(rng.sample(dist), 10);
        }
    }

    #[test]
    fn test_uniform_bad_limits_flipped_int() {
        assert_eq!(Uniform::new(10, 5), Err(Error::EmptyRange));
    }

    #[test]
    #[cfg_attr(miri, ignore)] // Miri is too slow
    fn test_integers() {
        let mut rng = crate::test::rng(251);
        macro_rules! t {
            ($ty:ident, $v:expr, $le:expr, $lt:expr) => {{
                for &(low, high) in $v.iter() {
                    let my_uniform = Uniform::new(low, high).unwrap();
                    for _ in 0..1000 {
                        let v: $ty = rng.sample(my_uniform);
                        assert!($le(low, v) && $lt(v, high));
                    }

                    let my_uniform = Uniform::new_inclusive(low, high).unwrap();
                    for _ in 0..1000 {
                        let v: $ty = rng.sample(my_uniform);
                        assert!($le(low, v) && $le(v, high));
                    }

                    let my_uniform = Uniform::new(&low, high).unwrap();
                    for _ in 0..1000 {
                        let v: $ty = rng.sample(my_uniform);
                        assert!($le(low, v) && $lt(v, high));
                    }

                    let my_uniform = Uniform::new_inclusive(&low, &high).unwrap();
                    for _ in 0..1000 {
                        let v: $ty = rng.sample(my_uniform);
                        assert!($le(low, v) && $le(v, high));
                    }

                    for _ in 0..1000 {
                        let v = <$ty as SampleUniform>::Sampler::sample_single(low, high, &mut rng).unwrap();
                        assert!($le(low, v) && $lt(v, high));
                    }

                    for _ in 0..1000 {
                        let v = <$ty as SampleUniform>::Sampler::sample_single_inclusive(low, high, &mut rng).unwrap();
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
                    |x: $ty, y| x.simd_le(y).all(),
                    |x: $ty, y| x.simd_lt(y).all()
                );)*
            }};
        }
        t!(i8, i16, i32, i64, u8, u16, u32, u64, i128, u128);

        #[cfg(feature = "simd_support")]
        {
            t!(u8x4, u8x8, u8x16, u8x32, u8x64 => u8);
            t!(i8x4, i8x8, i8x16, i8x32, i8x64 => i8);
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
        let r = Uniform::try_from(2u32..7).unwrap();
        assert_eq!(r.0.low, 2);
        assert_eq!(r.0.range, 5);
    }

    #[test]
    fn test_uniform_from_std_range_bad_limits() {
        #![allow(clippy::reversed_empty_ranges)]
        assert!(Uniform::try_from(100..10).is_err());
        assert!(Uniform::try_from(100..100).is_err());
    }

    #[test]
    fn test_uniform_from_std_range_inclusive() {
        let r = Uniform::try_from(2u32..=6).unwrap();
        assert_eq!(r.0.low, 2);
        assert_eq!(r.0.range, 5);
    }

    #[test]
    fn test_uniform_from_std_range_inclusive_bad_limits() {
        #![allow(clippy::reversed_empty_ranges)]
        assert!(Uniform::try_from(100..=10).is_err());
        assert!(Uniform::try_from(100..=99).is_err());
    }
}
