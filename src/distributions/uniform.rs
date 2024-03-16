// Copyright 2018-2020 Developers of the Rand project.
// Copyright 2017 The Rust Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A distribution uniformly sampling numbers within a given range.
//!
//! [`Uniform`] is the standard distribution to sample uniformly from a range;
//! e.g. `Uniform::new_inclusive(1, 6).unwrap()` can sample integers from 1 to 6, like a
//! standard die. [`Rng::gen_range`] supports any type supported by [`Uniform`].
//!
//! This distribution is provided with support for several primitive types
//! (all integer and floating-point types) as well as [`std::time::Duration`],
//! and supports extension to user-defined types via a type-specific *back-end*
//! implementation.
//!
//! The types [`UniformInt`], [`UniformFloat`] and [`UniformDuration`] are the
//! back-ends supporting sampling from primitive integer and floating-point
//! ranges as well as from [`std::time::Duration`]; these types do not normally
//! need to be used directly (unless implementing a derived back-end).
//!
//! # Example usage
//!
//! ```
//! use rand::{Rng, thread_rng};
//! use rand::distributions::Uniform;
//!
//! let mut rng = thread_rng();
//! let side = Uniform::new(-10.0, 10.0).unwrap();
//!
//! // sample between 1 and 10 points
//! for _ in 0..rng.gen_range(1..=10) {
//!     // sample a point from the square with sides -10 - 10 in two dimensions
//!     let (x, y) = (rng.sample(side), rng.sample(side));
//!     println!("Point: {}, {}", x, y);
//! }
//! ```
//!
//! # Extending `Uniform` to support a custom type
//!
//! To extend [`Uniform`] to support your own types, write a back-end which
//! implements the [`UniformSampler`] trait, then implement the [`SampleUniform`]
//! helper trait to "register" your back-end. See the `MyF32` example below.
//!
//! At a minimum, the back-end needs to store any parameters needed for sampling
//! (e.g. the target range) and implement `new`, `new_inclusive` and `sample`.
//! Those methods should include an assertion to check the range is valid (i.e.
//! `low < high`). The example below merely wraps another back-end.
//!
//! The `new`, `new_inclusive` and `sample_single` functions use arguments of
//! type `SampleBorrow<X>` to support passing in values by reference or
//! by value. In the implementation of these functions, you can choose to
//! simply use the reference returned by [`SampleBorrow::borrow`], or you can choose
//! to copy or clone the value, whatever is appropriate for your type.
//!
//! ```
//! use rand::prelude::*;
//! use rand::distributions::uniform::{Uniform, SampleUniform,
//!         UniformSampler, UniformFloat, SampleBorrow, Error};
//!
//! struct MyF32(f32);
//!
//! #[derive(Clone, Copy, Debug)]
//! struct UniformMyF32(UniformFloat<f32>);
//!
//! impl UniformSampler for UniformMyF32 {
//!     type X = MyF32;
//!
//!     fn new<B1, B2>(low: B1, high: B2) -> Result<Self, Error>
//!         where B1: SampleBorrow<Self::X> + Sized,
//!               B2: SampleBorrow<Self::X> + Sized
//!     {
//!         UniformFloat::<f32>::new(low.borrow().0, high.borrow().0).map(UniformMyF32)
//!     }
//!     fn new_inclusive<B1, B2>(low: B1, high: B2) -> Result<Self, Error>
//!         where B1: SampleBorrow<Self::X> + Sized,
//!               B2: SampleBorrow<Self::X> + Sized
//!     {
//!         UniformFloat::<f32>::new_inclusive(low.borrow().0, high.borrow().0).map(UniformMyF32)
//!     }
//!     fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
//!         MyF32(self.0.sample(rng))
//!     }
//! }
//!
//! impl SampleUniform for MyF32 {
//!     type Sampler = UniformMyF32;
//! }
//!
//! let (low, high) = (MyF32(17.0f32), MyF32(22.0f32));
//! let uniform = Uniform::new(low, high).unwrap();
//! let x = uniform.sample(&mut thread_rng());
//! ```
//!
//! [`SampleUniform`]: crate::distributions::uniform::SampleUniform
//! [`UniformSampler`]: crate::distributions::uniform::UniformSampler
//! [`UniformInt`]: crate::distributions::uniform::UniformInt
//! [`UniformFloat`]: crate::distributions::uniform::UniformFloat
//! [`UniformDuration`]: crate::distributions::uniform::UniformDuration
//! [`SampleBorrow::borrow`]: crate::distributions::uniform::SampleBorrow::borrow

use core::fmt;
use core::time::Duration;
use core::ops::{Range, RangeInclusive};

use crate::distributions::float::IntoFloat;
use crate::distributions::utils::{BoolAsSIMD, FloatAsSIMD, FloatSIMDUtils, IntAsSIMD, WideningMultiply};
use crate::distributions::Distribution;
#[cfg(feature = "simd_support")]
use crate::distributions::Standard;
use crate::{Rng, RngCore};

#[cfg(feature = "simd_support")] use core::simd::prelude::*;
#[cfg(feature = "simd_support")] use core::simd::{LaneCount, SupportedLaneCount};

/// Error type returned from [`Uniform::new`] and `new_inclusive`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// `low > high`, or equal in case of exclusive range.
    EmptyRange,
    /// Input or range `high - low` is non-finite. Not relevant to integer types.
    NonFinite,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::EmptyRange => "low > high (or equal if exclusive) in uniform distribution",
            Error::NonFinite => "Non-finite range in uniform distribution",
        })
    }
}

#[cfg(feature = "std")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "std")))]
impl std::error::Error for Error {}

#[cfg(feature = "serde1")]
use serde::{Serialize, Deserialize};

/// Sample values uniformly between two bounds.
///
/// [`Uniform::new`] and [`Uniform::new_inclusive`] construct a uniform
/// distribution sampling from the given range; these functions may do extra
/// work up front to make sampling of multiple values faster. If only one sample
/// from the range is required, [`Rng::gen_range`] can be more efficient.
///
/// When sampling from a constant range, many calculations can happen at
/// compile-time and all methods should be fast; for floating-point ranges and
/// the full range of integer types, this should have comparable performance to
/// the `Standard` distribution.
///
/// Steps are taken to avoid bias, which might be present in naive
/// implementations; for example `rng.gen::<u8>() % 170` samples from the range
/// `[0, 169]` but is twice as likely to select numbers less than 85 than other
/// values. Further, the implementations here give more weight to the high-bits
/// generated by the RNG than the low bits, since with some RNGs the low-bits
/// are of lower quality than the high bits.
///
/// Implementations must sample in `[low, high)` range for
/// `Uniform::new(low, high)`, i.e., excluding `high`. In particular, care must
/// be taken to ensure that rounding never results values `< low` or `>= high`.
///
/// # Example
///
/// ```
/// use rand::distributions::{Distribution, Uniform};
///
/// let between = Uniform::try_from(10..10000).unwrap();
/// let mut rng = rand::thread_rng();
/// let mut sum = 0;
/// for _ in 0..1000 {
///     sum += between.sample(&mut rng);
/// }
/// println!("{}", sum);
/// ```
///
/// For a single sample, [`Rng::gen_range`] may be preferred:
///
/// ```
/// use rand::Rng;
///
/// let mut rng = rand::thread_rng();
/// println!("{}", rng.gen_range(0..10));
/// ```
///
/// [`new`]: Uniform::new
/// [`new_inclusive`]: Uniform::new_inclusive
/// [`Rng::gen_range`]: Rng::gen_range
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "serde1", serde(bound(serialize = "X::Sampler: Serialize")))]
#[cfg_attr(feature = "serde1", serde(bound(deserialize = "X::Sampler: Deserialize<'de>")))]
pub struct Uniform<X: SampleUniform>(X::Sampler);

impl<X: SampleUniform> Uniform<X> {
    /// Create a new `Uniform` instance, which samples uniformly from the half
    /// open range `[low, high)` (excluding `high`).
    ///
    /// Fails if `low >= high`, or if `low`, `high` or the range `high - low` is
    /// non-finite. In release mode, only the range is checked.
    pub fn new<B1, B2>(low: B1, high: B2) -> Result<Uniform<X>, Error>
    where
        B1: SampleBorrow<X> + Sized,
        B2: SampleBorrow<X> + Sized,
    {
        X::Sampler::new(low, high).map(Uniform)
    }

    /// Create a new `Uniform` instance, which samples uniformly from the closed
    /// range `[low, high]` (inclusive).
    ///
    /// Fails if `low > high`, or if `low`, `high` or the range `high - low` is
    /// non-finite. In release mode, only the range is checked.
    pub fn new_inclusive<B1, B2>(low: B1, high: B2) -> Result<Uniform<X>, Error>
    where
        B1: SampleBorrow<X> + Sized,
        B2: SampleBorrow<X> + Sized,
    {
        X::Sampler::new_inclusive(low, high).map(Uniform)
    }
}

impl<X: SampleUniform> Distribution<X> for Uniform<X> {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> X {
        self.0.sample(rng)
    }
}

/// Helper trait for creating objects using the correct implementation of
/// [`UniformSampler`] for the sampling type.
///
/// See the [module documentation] on how to implement [`Uniform`] range
/// sampling for a custom type.
///
/// [module documentation]: crate::distributions::uniform
pub trait SampleUniform: Sized {
    /// The `UniformSampler` implementation supporting type `X`.
    type Sampler: UniformSampler<X = Self>;
}

/// Helper trait handling actual uniform sampling.
///
/// See the [module documentation] on how to implement [`Uniform`] range
/// sampling for a custom type.
///
/// Implementation of [`sample_single`] is optional, and is only useful when
/// the implementation can be faster than `Self::new(low, high).sample(rng)`.
///
/// [module documentation]: crate::distributions::uniform
/// [`sample_single`]: UniformSampler::sample_single
pub trait UniformSampler: Sized {
    /// The type sampled by this implementation.
    type X;

    /// Construct self, with inclusive lower bound and exclusive upper bound `[low, high)`.
    ///
    /// Usually users should not call this directly but prefer to use
    /// [`Uniform::new`].
    fn new<B1, B2>(low: B1, high: B2) -> Result<Self, Error>
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized;

    /// Construct self, with inclusive bounds `[low, high]`.
    ///
    /// Usually users should not call this directly but prefer to use
    /// [`Uniform::new_inclusive`].
    fn new_inclusive<B1, B2>(low: B1, high: B2) -> Result<Self, Error>
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized;

    /// Sample a value.
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X;

    /// Sample a single value uniformly from a range with inclusive lower bound
    /// and exclusive upper bound `[low, high)`.
    ///
    /// By default this is implemented using
    /// `UniformSampler::new(low, high).sample(rng)`. However, for some types
    /// more optimal implementations for single usage may be provided via this
    /// method (which is the case for integers and floats).
    /// Results may not be identical.
    ///
    /// Note that to use this method in a generic context, the type needs to be
    /// retrieved via `SampleUniform::Sampler` as follows:
    /// ```
    /// use rand::{thread_rng, distributions::uniform::{SampleUniform, UniformSampler}};
    /// # #[allow(unused)]
    /// fn sample_from_range<T: SampleUniform>(lb: T, ub: T) -> T {
    ///     let mut rng = thread_rng();
    ///     <T as SampleUniform>::Sampler::sample_single(lb, ub, &mut rng).unwrap()
    /// }
    /// ```
    fn sample_single<R: Rng + ?Sized, B1, B2>(low: B1, high: B2, rng: &mut R) -> Result<Self::X, Error>
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let uniform: Self = UniformSampler::new(low, high)?;
        Ok(uniform.sample(rng))
    }

    /// Sample a single value uniformly from a range with inclusive lower bound
    /// and inclusive upper bound `[low, high]`.
    ///
    /// By default this is implemented using
    /// `UniformSampler::new_inclusive(low, high).sample(rng)`. However, for
    /// some types more optimal implementations for single usage may be provided
    /// via this method.
    /// Results may not be identical.
    fn sample_single_inclusive<R: Rng + ?Sized, B1, B2>(low: B1, high: B2, rng: &mut R)
        -> Result<Self::X, Error>
        where B1: SampleBorrow<Self::X> + Sized,
              B2: SampleBorrow<Self::X> + Sized
    {
        let uniform: Self = UniformSampler::new_inclusive(low, high)?;
        Ok(uniform.sample(rng))
    }
}

impl<X: SampleUniform> TryFrom<Range<X>> for Uniform<X> {
    type Error = Error;

    fn try_from(r: ::core::ops::Range<X>) -> Result<Uniform<X>, Error> {
        Uniform::new(r.start, r.end)
    }
}

impl<X: SampleUniform> TryFrom<RangeInclusive<X>> for Uniform<X> {
    type Error = Error;

    fn try_from(r: ::core::ops::RangeInclusive<X>) -> Result<Uniform<X>, Error> {
        Uniform::new_inclusive(r.start(), r.end())
    }
}


/// Helper trait similar to [`Borrow`] but implemented
/// only for SampleUniform and references to SampleUniform in
/// order to resolve ambiguity issues.
///
/// [`Borrow`]: std::borrow::Borrow
pub trait SampleBorrow<Borrowed> {
    /// Immutably borrows from an owned value. See [`Borrow::borrow`]
    ///
    /// [`Borrow::borrow`]: std::borrow::Borrow::borrow
    fn borrow(&self) -> &Borrowed;
}
impl<Borrowed> SampleBorrow<Borrowed> for Borrowed
where Borrowed: SampleUniform
{
    #[inline(always)]
    fn borrow(&self) -> &Borrowed {
        self
    }
}
impl<'a, Borrowed> SampleBorrow<Borrowed> for &'a Borrowed
where Borrowed: SampleUniform
{
    #[inline(always)]
    fn borrow(&self) -> &Borrowed {
        self
    }
}

/// Range that supports generating a single sample efficiently.
///
/// Any type implementing this trait can be used to specify the sampled range
/// for `Rng::gen_range`.
pub trait SampleRange<T> {
    /// Generate a sample from the given range.
    fn sample_single<R: RngCore + ?Sized>(self, rng: &mut R) -> Result<T, Error>;

    /// Check whether the range is empty.
    fn is_empty(&self) -> bool;
}

impl<T: SampleUniform + PartialOrd> SampleRange<T> for Range<T> {
    #[inline]
    fn sample_single<R: RngCore + ?Sized>(self, rng: &mut R) -> Result<T, Error> {
        T::Sampler::sample_single(self.start, self.end, rng)
    }

    #[inline]
    fn is_empty(&self) -> bool {
        !(self.start < self.end)
    }
}

impl<T: SampleUniform + PartialOrd> SampleRange<T> for RangeInclusive<T> {
    #[inline]
    fn sample_single<R: RngCore + ?Sized>(self, rng: &mut R) -> Result<T, Error> {
        T::Sampler::sample_single_inclusive(self.start(), self.end(), rng)
    }

    #[inline]
    fn is_empty(&self) -> bool {
        !(self.start() <= self.end())
    }
}


////////////////////////////////////////////////////////////////////////////////

// What follows are all back-ends.


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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
pub struct UniformInt<X> {
    low: X,
    range: X,
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
                    range: range as $ty, // type: $uty
                    thresh: thresh as $uty as $ty, // type: $sample_ty
                })
            }

            /// Sample from distribution, Lemire's method, unbiased
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
            fn sample_single<R: Rng + ?Sized, B1, B2>(low_b: B1, high_b: B2, rng: &mut R) -> Result<Self::X, Error>
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
                low_b: B1, high_b: B2, rng: &mut R,
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
                    return Ok(rng.gen());
                }

                // generate a sample using a sensible integer type
                let (mut result, lo_order) = rng.gen::<$sample_ty>().wmul(range);

                // if the sample is biased...
                if lo_order > range.wrapping_neg() {
                    // ...generate a new sample to reduce bias...
                    let (new_hi_order, _) = (rng.gen::<$sample_ty>()).wmul(range as $sample_ty);
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
                low_b: B1, high_b: B2, rng: &mut R,
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
                    return Ok(rng.gen());
                }

                let (mut result, mut lo) = rng.gen::<$sample_ty>().wmul(range);

                // In contrast to the biased sampler, we use a loop:
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
uniform_int_impl! { isize, usize, usize }
uniform_int_impl! { u8, u8, u32 }
uniform_int_impl! { u16, u16, u32 }
uniform_int_impl! { u32, u32, u32 }
uniform_int_impl! { u64, u64, u64 }
uniform_int_impl! { usize, usize, usize }
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
        #[cfg_attr(doc_cfg, doc(cfg(feature = "simd_support")))]
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
        #[cfg_attr(doc_cfg, doc(cfg(feature = "simd_support")))]
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
                let unsigned_max = Simd::splat(::core::$unsigned::MAX);

                // NOTE: all `Simd` operations are inherently wrapping,
                //       see https://doc.rust-lang.org/std/simd/struct.Simd.html
                let range: Simd<$unsigned, LANES> = ((high - low) + Simd::splat(1)).cast();
                // `% 0` will panic at runtime.
                let not_full_range = range.simd_gt(Simd::splat(0));
                // replacing 0 with `unsigned_max` allows a faster `select`
                // with bitwise OR
                let modulo = not_full_range.select(range, unsigned_max);
                // wrapping addition
                // TODO: replace with `range.wrapping_neg() % module` when Simd supports this.
                let ints_to_reject = (Simd::splat(0) - range) % modulo;
                // When `range` is 0, `lo` of `v.wmul(range)` will always be
                // zero which means only one sample is needed.

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
                let mut v: Simd<$unsigned, LANES> = rng.gen();
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
                    v = mask.select(v, rng.gen());
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

impl SampleUniform for char {
    type Sampler = UniformChar;
}

/// The back-end implementing [`UniformSampler`] for `char`.
///
/// Unless you are implementing [`UniformSampler`] for your own type, this type
/// should not be used directly, use [`Uniform`] instead.
///
/// This differs from integer range sampling since the range `0xD800..=0xDFFF`
/// are used for surrogate pairs in UCS and UTF-16, and consequently are not
/// valid Unicode code points. We must therefore avoid sampling values in this
/// range.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
pub struct UniformChar {
    sampler: UniformInt<u32>,
}

/// UTF-16 surrogate range start
const CHAR_SURROGATE_START: u32 = 0xD800;
/// UTF-16 surrogate range size
const CHAR_SURROGATE_LEN: u32 = 0xE000 - CHAR_SURROGATE_START;

/// Convert `char` to compressed `u32`
fn char_to_comp_u32(c: char) -> u32 {
    match c as u32 {
        c if c >= CHAR_SURROGATE_START => c - CHAR_SURROGATE_LEN,
        c => c,
    }
}

impl UniformSampler for UniformChar {
    type X = char;

    #[inline] // if the range is constant, this helps LLVM to do the
              // calculations at compile-time.
    fn new<B1, B2>(low_b: B1, high_b: B2) -> Result<Self, Error>
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let low = char_to_comp_u32(*low_b.borrow());
        let high = char_to_comp_u32(*high_b.borrow());
        let sampler = UniformInt::<u32>::new(low, high);
        sampler.map(|sampler| UniformChar { sampler })
    }

    #[inline] // if the range is constant, this helps LLVM to do the
              // calculations at compile-time.
    fn new_inclusive<B1, B2>(low_b: B1, high_b: B2) -> Result<Self, Error>
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let low = char_to_comp_u32(*low_b.borrow());
        let high = char_to_comp_u32(*high_b.borrow());
        let sampler = UniformInt::<u32>::new_inclusive(low, high);
        sampler.map(|sampler| UniformChar { sampler })
    }

    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
        let mut x = self.sampler.sample(rng);
        if x >= CHAR_SURROGATE_START {
            x += CHAR_SURROGATE_LEN;
        }
        // SAFETY: x must not be in surrogate range or greater than char::MAX.
        // This relies on range constructors which accept char arguments.
        // Validity of input char values is assumed.
        unsafe { core::char::from_u32_unchecked(x) }
    }
}

/// Note: the `String` is potentially left with excess capacity if the range
/// includes non ascii chars; optionally the user may call
/// `string.shrink_to_fit()` afterwards.
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
impl super::DistString for Uniform<char> {
    fn append_string<R: Rng + ?Sized>(&self, rng: &mut R, string: &mut alloc::string::String, len: usize) {
        // Getting the hi value to assume the required length to reserve in string.
        let mut hi = self.0.sampler.low + self.0.sampler.range - 1;
        if hi >= CHAR_SURROGATE_START {
            hi += CHAR_SURROGATE_LEN;
        }
        // Get the utf8 length of hi to minimize extra space.
        let max_char_len = char::from_u32(hi).map(char::len_utf8).unwrap_or(4);
        string.reserve(max_char_len * len);
        string.extend(self.sample_iter(rng).take(len))
    }
}

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
    ($($meta:meta)?, $ty:ty, $uty:ident, $f_scalar:ident, $u_scalar:ident, $bits_to_discard:expr) => {
        $(#[cfg($meta)]
        #[cfg_attr(doc_cfg, doc(cfg($meta)))])?
        impl SampleUniform for $ty {
            type Sampler = UniformFloat<$ty>;
        }

        $(#[cfg($meta)]
        #[cfg_attr(doc_cfg, doc(cfg($meta)))])?
        impl UniformSampler for UniformFloat<$ty> {
            type X = $ty;

            fn new<B1, B2>(low_b: B1, high_b: B2) -> Result<Self, Error>
            where
                B1: SampleBorrow<Self::X> + Sized,
                B2: SampleBorrow<Self::X> + Sized,
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                #[cfg(debug_assertions)]
                if !(low.all_finite()) || !(high.all_finite()) {
                    return Err(Error::NonFinite);
                }
                if !(low.all_lt(high)) {
                    return Err(Error::EmptyRange);
                }
                let max_rand = <$ty>::splat(
                    (::core::$u_scalar::MAX >> $bits_to_discard).into_float_with_exponent(0) - 1.0,
                );

                let mut scale = high - low;
                if !(scale.all_finite()) {
                    return Err(Error::NonFinite);
                }

                loop {
                    let mask = (scale * max_rand + low).ge_mask(high);
                    if !mask.any() {
                        break;
                    }
                    scale = scale.decrease_masked(mask);
                }

                debug_assert!(<$ty>::splat(0.0).all_le(scale));

                Ok(UniformFloat { low, scale })
            }

            fn new_inclusive<B1, B2>(low_b: B1, high_b: B2) -> Result<Self, Error>
            where
                B1: SampleBorrow<Self::X> + Sized,
                B2: SampleBorrow<Self::X> + Sized,
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                #[cfg(debug_assertions)]
                if !(low.all_finite()) || !(high.all_finite()) {
                    return Err(Error::NonFinite);
                }
                if !low.all_le(high) {
                    return Err(Error::EmptyRange);
                }
                let max_rand = <$ty>::splat(
                    (::core::$u_scalar::MAX >> $bits_to_discard).into_float_with_exponent(0) - 1.0,
                );

                let mut scale = (high - low) / max_rand;
                if !scale.all_finite() {
                    return Err(Error::NonFinite);
                }

                loop {
                    let mask = (scale * max_rand + low).gt_mask(high);
                    if !mask.any() {
                        break;
                    }
                    scale = scale.decrease_masked(mask);
                }

                debug_assert!(<$ty>::splat(0.0).all_le(scale));

                Ok(UniformFloat { low, scale })
            }

            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
                // Generate a value in the range [1, 2)
                let value1_2 = (rng.gen::<$uty>() >> $uty::splat($bits_to_discard)).into_float_with_exponent(0);

                // Get a value in the range [0, 1) to avoid overflow when multiplying by scale
                let value0_1 = value1_2 - <$ty>::splat(1.0);

                // We don't use `f64::mul_add`, because it is not available with
                // `no_std`. Furthermore, it is slower for some targets (but
                // faster for others). However, the order of multiplication and
                // addition is important, because on some platforms (e.g. ARM)
                // it will be optimized to a single (non-FMA) instruction.
                value0_1 * self.scale + self.low
            }

            #[inline]
            fn sample_single<R: Rng + ?Sized, B1, B2>(low_b: B1, high_b: B2, rng: &mut R) -> Result<Self::X, Error>
            where
                B1: SampleBorrow<Self::X> + Sized,
                B2: SampleBorrow<Self::X> + Sized,
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                #[cfg(debug_assertions)]
                if !low.all_finite() || !high.all_finite() {
                    return Err(Error::NonFinite);
                }
                if !low.all_lt(high) {
                    return Err(Error::EmptyRange);
                }
                let mut scale = high - low;
                if !scale.all_finite() {
                    return Err(Error::NonFinite);
                }

                loop {
                    // Generate a value in the range [1, 2)
                    let value1_2 =
                        (rng.gen::<$uty>() >> $uty::splat($bits_to_discard)).into_float_with_exponent(0);

                    // Get a value in the range [0, 1) to avoid overflow when multiplying by scale
                    let value0_1 = value1_2 - <$ty>::splat(1.0);

                    // Doing multiply before addition allows some architectures
                    // to use a single instruction.
                    let res = value0_1 * scale + low;

                    debug_assert!(low.all_le(res) || !scale.all_finite());
                    if res.all_lt(high) {
                        return Ok(res);
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
                    // Likewise, `high - low` overflowing to infinity is also
                    // rare, so handle it here after the common case.
                    let mask = !scale.finite_mask();
                    if mask.any() {
                        if !(low.all_finite() && high.all_finite()) {
                            return Err(Error::NonFinite);
                        }
                        scale = scale.decrease_masked(mask);
                    }
                }
            }

            #[inline]
            fn sample_single_inclusive<R: Rng + ?Sized, B1, B2>(low_b: B1, high_b: B2, rng: &mut R) -> Result<Self::X, Error>
            where
                B1: SampleBorrow<Self::X> + Sized,
                B2: SampleBorrow<Self::X> + Sized,
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                #[cfg(debug_assertions)]
                if !low.all_finite() || !high.all_finite() {
                    return Err(Error::NonFinite);
                }
                if !low.all_le(high) {
                    return Err(Error::EmptyRange);
                }
                let scale = high - low;
                if !scale.all_finite() {
                    return Err(Error::NonFinite);
                }

                // Generate a value in the range [1, 2)
                let value1_2 =
                    (rng.gen::<$uty>() >> $uty::splat($bits_to_discard)).into_float_with_exponent(0);

                // Get a value in the range [0, 1) to avoid overflow when multiplying by scale
                let value0_1 = value1_2 - <$ty>::splat(1.0);

                // Doing multiply before addition allows some architectures
                // to use a single instruction.
                Ok(value0_1 * scale + low)
            }
        }
    };
}

uniform_float_impl! { , f32, u32, f32, u32, 32 - 23 }
uniform_float_impl! { , f64, u64, f64, u64, 64 - 52 }

#[cfg(feature = "simd_support")]
uniform_float_impl! { feature = "simd_support", f32x2, u32x2, f32, u32, 32 - 23 }
#[cfg(feature = "simd_support")]
uniform_float_impl! { feature = "simd_support", f32x4, u32x4, f32, u32, 32 - 23 }
#[cfg(feature = "simd_support")]
uniform_float_impl! { feature = "simd_support", f32x8, u32x8, f32, u32, 32 - 23 }
#[cfg(feature = "simd_support")]
uniform_float_impl! { feature = "simd_support", f32x16, u32x16, f32, u32, 32 - 23 }

#[cfg(feature = "simd_support")]
uniform_float_impl! { feature = "simd_support", f64x2, u64x2, f64, u64, 64 - 52 }
#[cfg(feature = "simd_support")]
uniform_float_impl! { feature = "simd_support", f64x4, u64x4, f64, u64, 64 - 52 }
#[cfg(feature = "simd_support")]
uniform_float_impl! { feature = "simd_support", f64x8, u64x8, f64, u64, 64 - 52 }


/// The back-end implementing [`UniformSampler`] for `Duration`.
///
/// Unless you are implementing [`UniformSampler`] for your own types, this type
/// should not be used directly, use [`Uniform`] instead.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
pub struct UniformDuration {
    mode: UniformDurationMode,
    offset: u32,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
enum UniformDurationMode {
    Small {
        secs: u64,
        nanos: Uniform<u32>,
    },
    Medium {
        nanos: Uniform<u64>,
    },
    Large {
        max_secs: u64,
        max_nanos: u32,
        secs: Uniform<u64>,
    },
}

impl SampleUniform for Duration {
    type Sampler = UniformDuration;
}

impl UniformSampler for UniformDuration {
    type X = Duration;

    #[inline]
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
        UniformDuration::new_inclusive(low, high - Duration::new(0, 1))
    }

    #[inline]
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

        let low_s = low.as_secs();
        let low_n = low.subsec_nanos();
        let mut high_s = high.as_secs();
        let mut high_n = high.subsec_nanos();

        if high_n < low_n {
            high_s -= 1;
            high_n += 1_000_000_000;
        }

        let mode = if low_s == high_s {
            UniformDurationMode::Small {
                secs: low_s,
                nanos: Uniform::new_inclusive(low_n, high_n)?,
            }
        } else {
            let max = high_s
                .checked_mul(1_000_000_000)
                .and_then(|n| n.checked_add(u64::from(high_n)));

            if let Some(higher_bound) = max {
                let lower_bound = low_s * 1_000_000_000 + u64::from(low_n);
                UniformDurationMode::Medium {
                    nanos: Uniform::new_inclusive(lower_bound, higher_bound)?,
                }
            } else {
                // An offset is applied to simplify generation of nanoseconds
                let max_nanos = high_n - low_n;
                UniformDurationMode::Large {
                    max_secs: high_s,
                    max_nanos,
                    secs: Uniform::new_inclusive(low_s, high_s)?,
                }
            }
        };
        Ok(UniformDuration {
            mode,
            offset: low_n,
        })
    }

    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Duration {
        match self.mode {
            UniformDurationMode::Small { secs, nanos } => {
                let n = nanos.sample(rng);
                Duration::new(secs, n)
            }
            UniformDurationMode::Medium { nanos } => {
                let nanos = nanos.sample(rng);
                Duration::new(nanos / 1_000_000_000, (nanos % 1_000_000_000) as u32)
            }
            UniformDurationMode::Large {
                max_secs,
                max_nanos,
                secs,
            } => {
                // constant folding means this is at least as fast as `Rng::sample(Range)`
                let nano_range = Uniform::new(0, 1_000_000_000).unwrap();
                loop {
                    let s = secs.sample(rng);
                    let n = nano_range.sample(rng);
                    if !(s == max_secs && n > max_nanos) {
                        let sum = n + self.offset;
                        break Duration::new(s, sum);
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rngs::mock::StepRng;
    use crate::distributions::utils::FloatSIMDScalarUtils;

    #[test]
    #[cfg(feature = "serde1")]
    fn test_serialization_uniform_duration() {
        let distr = UniformDuration::new(Duration::from_secs(10), Duration::from_secs(60)).unwrap();
        let de_distr: UniformDuration = bincode::deserialize(&bincode::serialize(&distr).unwrap()).unwrap();
        assert_eq!(distr, de_distr);
    }

    #[test]
    #[cfg(feature = "serde1")]
    fn test_uniform_serialization() {
        let unit_box: Uniform<i32>  = Uniform::new(-1, 1).unwrap();
        let de_unit_box: Uniform<i32> = bincode::deserialize(&bincode::serialize(&unit_box).unwrap()).unwrap();
        assert_eq!(unit_box.0, de_unit_box.0);

        let unit_box: Uniform<f32> = Uniform::new(-1., 1.).unwrap();
        let de_unit_box: Uniform<f32> = bincode::deserialize(&bincode::serialize(&unit_box).unwrap()).unwrap();
        assert_eq!(unit_box.0, de_unit_box.0);
    }

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
        use core::{i128, u128};
        use core::{i16, i32, i64, i8, isize};
        use core::{u16, u32, u64, u8, usize};

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
        t!(i8, i16, i32, i64, isize, u8, u16, u32, u64, usize, i128, u128);

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
    #[cfg_attr(miri, ignore)] // Miri is too slow
    fn test_char() {
        let mut rng = crate::test::rng(891);
        let mut max = core::char::from_u32(0).unwrap();
        for _ in 0..100 {
            let c = rng.gen_range('A'..='Z');
            assert!(('A'..='Z').contains(&c));
            max = max.max(c);
        }
        assert_eq!(max, 'Z');
        let d = Uniform::new(
            core::char::from_u32(0xD7F0).unwrap(),
            core::char::from_u32(0xE010).unwrap(),
        ).unwrap();
        for _ in 0..100 {
            let c = d.sample(&mut rng);
            assert!((c as u32) < 0xD800 || (c as u32) > 0xDFFF);
        }
        #[cfg(feature = "alloc")]
        {
            use crate::distributions::DistString;
            let string1 = d.sample_string(&mut rng, 100);
            assert_eq!(string1.capacity(), 300);
            let string2 = Uniform::new(
                core::char::from_u32(0x0000).unwrap(),
                core::char::from_u32(0x0080).unwrap(),
            ).unwrap().sample_string(&mut rng, 100);
            assert_eq!(string2.capacity(), 100);
            let string3 = Uniform::new_inclusive(
                core::char::from_u32(0x0000).unwrap(),
                core::char::from_u32(0x0080).unwrap(),
            ).unwrap().sample_string(&mut rng, 100);
            assert_eq!(string3.capacity(), 200);
        }
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
                    for lane in 0..<$ty>::LEN {
                        let low = <$ty>::splat(0.0 as $f_scalar).replace(lane, low_scalar);
                        let high = <$ty>::splat(1.0 as $f_scalar).replace(lane, high_scalar);
                        let my_uniform = Uniform::new(low, high).unwrap();
                        let my_incl_uniform = Uniform::new_inclusive(low, high).unwrap();
                        for _ in 0..100 {
                            let v = rng.sample(my_uniform).extract(lane);
                            assert!(low_scalar <= v && v < high_scalar);
                            let v = rng.sample(my_incl_uniform).extract(lane);
                            assert!(low_scalar <= v && v <= high_scalar);
                            let v = <$ty as SampleUniform>::Sampler
                                ::sample_single(low, high, &mut rng).unwrap().extract(lane);
                            assert!(low_scalar <= v && v < high_scalar);
                            let v = <$ty as SampleUniform>::Sampler
                                ::sample_single_inclusive(low, high, &mut rng).unwrap().extract(lane);
                            assert!(low_scalar <= v && v <= high_scalar);
                        }

                        assert_eq!(
                            rng.sample(Uniform::new_inclusive(low, low).unwrap()).extract(lane),
                            low_scalar
                        );

                        assert_eq!(zero_rng.sample(my_uniform).extract(lane), low_scalar);
                        assert_eq!(zero_rng.sample(my_incl_uniform).extract(lane), low_scalar);
                        assert_eq!(<$ty as SampleUniform>::Sampler
                            ::sample_single(low, high, &mut zero_rng).unwrap()
                            .extract(lane), low_scalar);
                        assert_eq!(<$ty as SampleUniform>::Sampler
                            ::sample_single_inclusive(low, high, &mut zero_rng).unwrap()
                            .extract(lane), low_scalar);

                        assert!(max_rng.sample(my_uniform).extract(lane) < high_scalar);
                        assert!(max_rng.sample(my_incl_uniform).extract(lane) <= high_scalar);
                        // sample_single cannot cope with max_rng:
                        // assert!(<$ty as SampleUniform>::Sampler
                        //     ::sample_single(low, high, &mut max_rng).unwrap()
                        //     .extract(lane) < high_scalar);
                        assert!(<$ty as SampleUniform>::Sampler
                            ::sample_single_inclusive(low, high, &mut max_rng).unwrap()
                            .extract(lane) <= high_scalar);

                        // Don't run this test for really tiny differences between high and low
                        // since for those rounding might result in selecting high for a very
                        // long time.
                        if (high_scalar - low_scalar) > 0.0001 {
                            let mut lowering_max_rng = StepRng::new(
                                0xffff_ffff_ffff_ffff,
                                (-1i64 << $bits_shifted) as u64,
                            );
                            assert!(
                                <$ty as SampleUniform>::Sampler
                                    ::sample_single(low, high, &mut lowering_max_rng).unwrap()
                                    .extract(lane) < high_scalar
                            );
                        }
                    }
                }

                assert_eq!(
                    rng.sample(Uniform::new_inclusive(
                        ::core::$f_scalar::MAX,
                        ::core::$f_scalar::MAX
                    ).unwrap()),
                    ::core::$f_scalar::MAX
                );
                assert_eq!(
                    rng.sample(Uniform::new_inclusive(
                        -::core::$f_scalar::MAX,
                        -::core::$f_scalar::MAX
                    ).unwrap()),
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
    fn test_float_overflow() {
        assert_eq!(Uniform::try_from(::core::f64::MIN..::core::f64::MAX), Err(Error::NonFinite));
    }

    #[test]
    #[should_panic]
    fn test_float_overflow_single() {
        let mut rng = crate::test::rng(252);
        rng.gen_range(::core::f64::MIN..::core::f64::MAX);
    }

    #[test]
    #[cfg(all(feature = "std", panic = "unwind"))]
    fn test_float_assertions() {
        use super::SampleUniform;
        use std::panic::catch_unwind;
        fn range<T: SampleUniform>(low: T, high: T) {
            let mut rng = crate::test::rng(253);
            T::Sampler::sample_single(low, high, &mut rng).unwrap();
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
                    for lane in 0..<$ty>::LEN {
                        let low = <$ty>::splat(0.0 as $f_scalar).replace(lane, low_scalar);
                        let high = <$ty>::splat(1.0 as $f_scalar).replace(lane, high_scalar);
                        assert!(catch_unwind(|| range(low, high)).is_err());
                        assert!(Uniform::new(low, high).is_err());
                        assert!(Uniform::new_inclusive(low, high).is_err());
                        assert!(catch_unwind(|| range(low, low)).is_err());
                        assert!(Uniform::new(low, low).is_err());
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
    #[cfg_attr(miri, ignore)] // Miri is too slow
    fn test_durations() {
        let mut rng = crate::test::rng(253);

        let v = &[
            (Duration::new(10, 50000), Duration::new(100, 1234)),
            (Duration::new(0, 100), Duration::new(1, 50)),
            (
                Duration::new(0, 0),
                Duration::new(u64::max_value(), 999_999_999),
            ),
        ];
        for &(low, high) in v.iter() {
            let my_uniform = Uniform::new(low, high).unwrap();
            for _ in 0..1000 {
                let v = rng.sample(my_uniform);
                assert!(low <= v && v < high);
            }
        }
    }

    #[test]
    fn test_custom_uniform() {
        use crate::distributions::uniform::{
            SampleBorrow, SampleUniform, UniformFloat, UniformSampler,
        };
        #[derive(Clone, Copy, PartialEq, PartialOrd)]
        struct MyF32 {
            x: f32,
        }
        #[derive(Clone, Copy, Debug)]
        struct UniformMyF32(UniformFloat<f32>);
        impl UniformSampler for UniformMyF32 {
            type X = MyF32;

            fn new<B1, B2>(low: B1, high: B2) -> Result<Self, Error>
            where
                B1: SampleBorrow<Self::X> + Sized,
                B2: SampleBorrow<Self::X> + Sized,
            {
                UniformFloat::<f32>::new(low.borrow().x, high.borrow().x).map(UniformMyF32)
            }

            fn new_inclusive<B1, B2>(low: B1, high: B2) -> Result<Self, Error>
            where
                B1: SampleBorrow<Self::X> + Sized,
                B2: SampleBorrow<Self::X> + Sized,
            {
                UniformSampler::new(low, high)
            }

            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
                MyF32 {
                    x: self.0.sample(rng),
                }
            }
        }
        impl SampleUniform for MyF32 {
            type Sampler = UniformMyF32;
        }

        let (low, high) = (MyF32 { x: 17.0f32 }, MyF32 { x: 22.0f32 });
        let uniform = Uniform::new(low, high).unwrap();
        let mut rng = crate::test::rng(804);
        for _ in 0..100 {
            let x: MyF32 = rng.sample(uniform);
            assert!(low <= x && x < high);
        }
    }

    #[test]
    fn test_uniform_from_std_range() {
        let r = Uniform::try_from(2u32..7).unwrap();
        assert_eq!(r.0.low, 2);
        assert_eq!(r.0.range, 5);
        let r = Uniform::try_from(2.0f64..7.0).unwrap();
        assert_eq!(r.0.low, 2.0);
        assert_eq!(r.0.scale, 5.0);
    }

    #[test]
    fn test_uniform_from_std_range_bad_limits() {
        #![allow(clippy::reversed_empty_ranges)]
        assert!(Uniform::try_from(100..10).is_err());
        assert!(Uniform::try_from(100..100).is_err());
        assert!(Uniform::try_from(100.0..10.0).is_err());
        assert!(Uniform::try_from(100.0..100.0).is_err());
    }

    #[test]
    fn test_uniform_from_std_range_inclusive() {
        let r = Uniform::try_from(2u32..=6).unwrap();
        assert_eq!(r.0.low, 2);
        assert_eq!(r.0.range, 5);
        let r = Uniform::try_from(2.0f64..=7.0).unwrap();
        assert_eq!(r.0.low, 2.0);
        assert!(r.0.scale > 5.0);
        assert!(r.0.scale < 5.0 + 1e-14);
    }

    #[test]
    fn test_uniform_from_std_range_inclusive_bad_limits() {
        #![allow(clippy::reversed_empty_ranges)]
        assert!(Uniform::try_from(100..=10).is_err());
        assert!(Uniform::try_from(100..=99).is_err());
        assert!(Uniform::try_from(100.0..=10.0).is_err());
        assert!(Uniform::try_from(100.0..=99.0).is_err());
    }

    #[test]
    fn value_stability() {
        fn test_samples<T: SampleUniform + Copy + core::fmt::Debug + PartialEq>(
            lb: T, ub: T, expected_single: &[T], expected_multiple: &[T],
        ) where Uniform<T>: Distribution<T> {
            let mut rng = crate::test::rng(897);
            let mut buf = [lb; 3];

            for x in &mut buf {
                *x = T::Sampler::sample_single(lb, ub, &mut rng).unwrap();
            }
            assert_eq!(&buf, expected_single);

            let distr = Uniform::new(lb, ub).unwrap();
            for x in &mut buf {
                *x = rng.sample(&distr);
            }
            assert_eq!(&buf, expected_multiple);
        }

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

        test_samples(
            Duration::new(2, 0),
            Duration::new(4, 0),
            &[
                Duration::new(2, 532615131),
                Duration::new(3, 638826742),
                Duration::new(3, 485707508),
            ],
            &[
                Duration::new(3, 117337521),
                Duration::new(3, 191764285),
                Duration::new(3, 236507617),
            ],
        );
    }

    #[test]
    fn uniform_distributions_can_be_compared() {
        assert_eq!(Uniform::new(1.0, 2.0).unwrap(), Uniform::new(1.0, 2.0).unwrap());

        // To cover UniformInt
        assert_eq!(Uniform::new(1_u32, 2_u32).unwrap(), Uniform::new(1_u32, 2_u32).unwrap());
    }
}
