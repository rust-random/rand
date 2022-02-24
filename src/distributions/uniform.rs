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
//! e.g. `Uniform::new_inclusive(1, 6)` can sample integers from 1 to 6, like a
//! standard die. [`Rng::gen_range`] supports any type supported by
//! [`Uniform`].
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
//! let side = Uniform::new(-10.0, 10.0);
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
//! Those methods should include an assert to check the range is valid (i.e.
//! `low < high`). The example below merely wraps another back-end.
//!
//! The `new`, `new_inclusive` and `sample_single` functions use arguments of
//! type SampleBorrow<X> in order to support passing in values by reference or
//! by value. In the implementation of these functions, you can choose to
//! simply use the reference returned by [`SampleBorrow::borrow`], or you can choose
//! to copy or clone the value, whatever is appropriate for your type.
//!
//! ```
//! use rand::prelude::*;
//! use rand::distributions::uniform::{Uniform, SampleUniform,
//!         UniformSampler, UniformFloat, SampleBorrow};
//!
//! struct MyF32(f32);
//!
//! #[derive(Clone, Copy, Debug)]
//! struct UniformMyF32(UniformFloat<f32>);
//!
//! impl UniformSampler for UniformMyF32 {
//!     type X = MyF32;
//!     fn new<B1, B2>(low: B1, high: B2) -> Self
//!         where B1: SampleBorrow<Self::X> + Sized,
//!               B2: SampleBorrow<Self::X> + Sized
//!     {
//!         UniformMyF32(UniformFloat::<f32>::new(low.borrow().0, high.borrow().0))
//!     }
//!     fn new_inclusive<B1, B2>(low: B1, high: B2) -> Self
//!         where B1: SampleBorrow<Self::X> + Sized,
//!               B2: SampleBorrow<Self::X> + Sized
//!     {
//!         UniformMyF32(UniformFloat::<f32>::new_inclusive(
//!             low.borrow().0,
//!             high.borrow().0,
//!         ))
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
//! let uniform = Uniform::new(low, high);
//! let x = uniform.sample(&mut thread_rng());
//! ```
//!
//! [`SampleUniform`]: crate::distributions::uniform::SampleUniform
//! [`UniformSampler`]: crate::distributions::uniform::UniformSampler
//! [`UniformInt`]: crate::distributions::uniform::UniformInt
//! [`UniformFloat`]: crate::distributions::uniform::UniformFloat
//! [`UniformDuration`]: crate::distributions::uniform::UniformDuration
//! [`SampleBorrow::borrow`]: crate::distributions::uniform::SampleBorrow::borrow

use core::ops::{Range, RangeInclusive};

use crate::distributions::utils::WideningMultiply;
use crate::distributions::Distribution;
use crate::{Rng, RngCore};

#[cfg(not(feature = "std"))]
#[allow(unused_imports)] // rustc doesn't detect that this is actually used
use crate::distributions::utils::Float;

#[cfg(feature = "simd_support")] use packed_simd::*;

#[cfg(feature = "serde1")] use serde::{Deserialize, Serialize};

mod uniform_float;
mod uniform_other;

pub use uniform_float::UniformFloat;
pub use uniform_other::{UniformChar, UniformDuration};

/// Sample values uniformly between two bounds.
///
/// [`Uniform::new`] and [`Uniform::new_inclusive`] construct a uniform
/// distribution sampling from the given range; these functions may do extra
/// work up front to make sampling of multiple values faster. If only one sample
/// from the range is required, [`Rng::gen_range`] can be more efficient.
///
/// When sampling from a constant range, many calculations can happen at
/// compile-time and all methods should be fast; for floating-point ranges and
/// the full range of integer types this should have comparable performance to
/// the `Standard` distribution.
///
/// Steps are taken to avoid bias which might be present in naive
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
/// let between = Uniform::from(10..10000);
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
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "serde1", serde(bound(serialize = "X::Sampler: Serialize")))]
#[cfg_attr(
    feature = "serde1",
    serde(bound(deserialize = "X::Sampler: Deserialize<'de>"))
)]
pub struct Uniform<X: SampleUniform>(X::Sampler);

impl<X: SampleUniform> Uniform<X> {
    /// Create a new `Uniform` instance which samples uniformly from the half
    /// open range `[low, high)` (excluding `high`). Panics if `low >= high`.
    pub fn new<B1, B2>(low: B1, high: B2) -> Uniform<X>
    where
        B1: SampleBorrow<X> + Sized,
        B2: SampleBorrow<X> + Sized,
    {
        Uniform(X::Sampler::new(low, high))
    }

    /// Create a new `Uniform` instance which samples uniformly from the closed
    /// range `[low, high]` (inclusive). Panics if `low > high`.
    pub fn new_inclusive<B1, B2>(low: B1, high: B2) -> Uniform<X>
    where
        B1: SampleBorrow<X> + Sized,
        B2: SampleBorrow<X> + Sized,
    {
        Uniform(X::Sampler::new_inclusive(low, high))
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

    /// Construct self, with inclusive lower bound and exclusive upper bound
    /// `[low, high)`.
    ///
    /// Usually users should not call this directly but instead use
    /// `Uniform::new`, which asserts that `low < high` before calling this.
    fn new<B1, B2>(low: B1, high: B2) -> Self
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized;

    /// Construct self, with inclusive bounds `[low, high]`.
    ///
    /// Usually users should not call this directly but instead use
    /// `Uniform::new_inclusive`, which asserts that `low <= high` before
    /// calling this.
    fn new_inclusive<B1, B2>(low: B1, high: B2) -> Self
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
    ///     <T as SampleUniform>::Sampler::sample_single(lb, ub, &mut rng)
    /// }
    /// ```
    fn sample_single<R: Rng + ?Sized, B1, B2>(low: B1, high: B2, rng: &mut R) -> Self::X
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let uniform: Self = UniformSampler::new(low, high);
        uniform.sample(rng)
    }

    /// Sample a single value uniformly from a range with inclusive lower bound
    /// and inclusive upper bound `[low, high]`.
    ///
    /// By default this is implemented using
    /// `UniformSampler::new_inclusive(low, high).sample(rng)`. However, for
    /// some types more optimal implementations for single usage may be provided
    /// via this method.
    /// Results may not be identical.
    fn sample_single_inclusive<R: Rng + ?Sized, B1, B2>(low: B1, high: B2, rng: &mut R) -> Self::X
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let uniform: Self = UniformSampler::new_inclusive(low, high);
        uniform.sample(rng)
    }
}

impl<X: SampleUniform> From<Range<X>> for Uniform<X> {
    fn from(r: ::core::ops::Range<X>) -> Uniform<X> {
        Uniform::new(r.start, r.end)
    }
}

impl<X: SampleUniform> From<RangeInclusive<X>> for Uniform<X> {
    fn from(r: ::core::ops::RangeInclusive<X>) -> Uniform<X> {
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
        *self
    }
}

/// Range that supports generating a single sample efficiently.
///
/// Any type implementing this trait can be used to specify the sampled range
/// for `Rng::gen_range`.
pub trait SampleRange<T> {
    /// Generate a sample from the given range.
    fn sample_single<R: RngCore + ?Sized>(self, rng: &mut R) -> T;

    /// Check whether the range is empty.
    fn is_empty(&self) -> bool;
}

impl<T: SampleUniform + PartialOrd> SampleRange<T> for Range<T> {
    #[inline]
    fn sample_single<R: RngCore + ?Sized>(self, rng: &mut R) -> T {
        T::Sampler::sample_single(self.start, self.end, rng)
    }

    #[inline]
    fn is_empty(&self) -> bool {
        !(self.start < self.end)
    }
}

impl<T: SampleUniform + PartialOrd> SampleRange<T> for RangeInclusive<T> {
    #[inline]
    fn sample_single<R: RngCore + ?Sized>(self, rng: &mut R) -> T {
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
    z: X, // either ints_to_reject or zone depending on implementation
}

macro_rules! uniform_int_impl {
    ($ty:ty, $unsigned:ident, $u_large:ident) => {
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
                    z: ints_to_reject as $unsigned as $ty,
                }
            }

            #[inline]
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
                let range = self.range as $unsigned as $u_large;
                if range > 0 {
                    let unsigned_max = ::core::$u_large::MAX;
                    let zone = unsigned_max - (self.z as $unsigned as $u_large);
                    loop {
                        let v: $u_large = rng.gen();
                        let (hi, lo) = v.wmul(range);
                        if lo <= zone {
                            return self.low.wrapping_add(hi as $ty);
                        }
                    }
                } else {
                    // Sample from the entire integer range.
                    rng.gen()
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
                // If the above resulted in wrap-around to 0, the range is $ty::MIN..=$ty::MAX,
                // and any integer will do.
                if range == 0 {
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
    };

    // bulk implementation
    ($(($unsigned:ident, $signed:ident),)+ $u_scalar:ident) => {
        $(
            uniform_simd_int_impl!($unsigned, $unsigned, $u_scalar);
            uniform_simd_int_impl!($signed, $unsigned, $u_scalar);
        )+
    };
}

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


#[cfg(test)]
mod tests {
    use super::*;

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

            fn new<B1, B2>(low: B1, high: B2) -> Self
            where
                B1: SampleBorrow<Self::X> + Sized,
                B2: SampleBorrow<Self::X> + Sized,
            {
                UniformMyF32(UniformFloat::<f32>::new(low.borrow().x, high.borrow().x))
            }

            fn new_inclusive<B1, B2>(low: B1, high: B2) -> Self
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
        let uniform = Uniform::new(low, high);
        let mut rng = crate::test::rng(804);
        for _ in 0..100 {
            let x: MyF32 = rng.sample(uniform);
            assert!(low <= x && x < high);
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

    pub(crate) fn test_samples<T: SampleUniform + Copy + core::fmt::Debug + PartialEq>(
        lb: T, ub: T, expected_single: &[T], expected_multiple: &[T],
    ) where Uniform<T>: Distribution<T> {
        let mut rng = crate::test::rng(897);
        let mut buf = [lb; 3];

        for x in &mut buf {
            *x = T::Sampler::sample_single(lb, ub, &mut rng);
        }
        assert_eq!(&buf, expected_single);

        let distr = Uniform::new(lb, ub);
        for x in &mut buf {
            *x = rng.sample(&distr);
        }
        assert_eq!(&buf, expected_multiple);
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
