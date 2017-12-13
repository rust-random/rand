// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A distribution generating numbers within a given range.

use Rand;
use Rng;
use distributions::{Distribution, Uniform};
use utils::FloatConversions;

/// Sample values uniformly between two bounds.
///
/// This gives a uniform distribution (assuming the RNG used to sample
/// it is itself uniform and the `RangeImpl` implementation is correct),
/// even for edge cases like `low = 0u8`,
/// `high = 170u8`, for which a naive modulo operation would return
/// numbers less than 85 with double the probability to those greater
/// than 85.
///
/// Types should attempt to sample in `[low, high)` for
/// `Range::new(low, high)`, i.e., excluding `high`, but this may be very
/// difficult. All the primitive integer types satisfy this property, and the
/// float types normally satisfy it, but rounding may mean `high` can occur.
///
/// # Example
///
/// ```rust
/// use rand::distributions::{Distribution, Range};
///
/// fn main() {
///     let between = Range::new(10, 10000);
///     let mut rng = rand::thread_rng();
///     let mut sum = 0;
///     for _ in 0..1000 {
///         sum += between.sample(&mut rng);
///     }
///     println!("{}", sum);
/// }
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Range<T: RangeImpl> {
    inner: T,
}

/// Ignore the `RangeInt<i32>` parameterisation; these non-member functions are
/// available to all range types. (Rust requires a type, and won't accept
/// `T: RangeImpl`. Consider this a minor language issue.)
impl Range<RangeInt<i32>> {
    /// Create a new `Range` instance which samples uniformly from the half
    /// open range `[low, high)` (excluding `high`). Panics if `low >= high`.
    pub fn new<X: SampleRange>(low: X, high: X) -> Range<X::T> {
        assert!(low < high, "Range::new called with `low >= high`");
        Range { inner: RangeImpl::new(low, high) }
    }

    /// Create a new `Range` instance which samples uniformly from the closed
    /// range `[low, high]` (inclusive). Panics if `low >= high`.
    pub fn new_inclusive<X: SampleRange>(low: X, high: X) -> Range<X::T> {
        assert!(low < high, "Range::new called with `low >= high`");
        Range { inner: RangeImpl::new_inclusive(low, high) }
    }

    /// Sample a single value uniformly from `[low, high)`.
    /// Panics if `low >= high`.
    pub fn sample_single<X: SampleRange, R: Rng+?Sized>(low: X, high: X, rng: &mut R) -> X {
        assert!(low < high, "Range::sample_single called with low >= high");
        X::T::sample_single(low, high, rng)
    }
}

impl<T: RangeImpl> Distribution<T::X> for Range<T> {
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> T::X {
        self.inner.sample(rng)
    }
}

/// Helper trait for creating objects using the correct implementation of
/// `RangeImpl` for the sampling type; this enables `Range::new(a, b)` to work.
pub trait SampleRange: PartialOrd+Sized {
    type T: RangeImpl<X = Self>;
}

/// Helper trait handling actual range sampling.
/// 
/// If you want to implement `Range` sampling for your own type, then
/// implement both this trait and `SampleRange`:
/// 
/// ```rust
/// use rand::{Rng, thread_rng, Distribution};
/// use rand::distributions::range::{Range, SampleRange, RangeImpl, RangeFloat};
/// 
/// #[derive(Clone, Copy, PartialEq, PartialOrd)]
/// struct MyF32(f32);
/// 
/// #[derive(Clone, Copy, Debug)]
/// struct RangeMyF32 {
///     inner: RangeFloat<f32>,
/// }
/// impl RangeImpl for RangeMyF32 {
///     type X = MyF32;
///     fn new(low: Self::X, high: Self::X) -> Self {
///         RangeMyF32 {
///             inner: RangeFloat::<f32>::new(low.0, high.0),
///         }
///     }
///     fn new_inclusive(low: Self::X, high: Self::X) -> Self {
///         RangeImpl::new(low, high)
///     }
///     fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> Self::X {
///         MyF32(self.inner.sample(rng))
///     }
/// }
/// 
/// impl SampleRange for MyF32 {
///     type T = RangeMyF32;
/// }
/// 
/// let (low, high) = (MyF32(17.0f32), MyF32(22.0f32));
/// let range = Range::new(low, high);
/// let x = range.sample(&mut thread_rng());
/// ```
pub trait RangeImpl: Sized {
    /// The type sampled by this implementation.
    type X: PartialOrd;

    /// Construct self, with inclusive lower bound and exclusive upper bound
    /// `[low, high)`.
    ///
    /// Usually users should not call this directly but instead use
    /// `Range::new`, which asserts that `low < high` before calling this.
    fn new(low: Self::X, high: Self::X) -> Self;

    /// Construct self, with inclusive bounds `[low, high]`.
    ///
    /// Usually users should not call this directly but instead use
    /// `Range::new`, which asserts that `low < high` before calling this.
    fn new_inclusive(low: Self::X, high: Self::X) -> Self;

    /// Sample a value.
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> Self::X;

    /// Sample a single value uniformly from a range with inclusive lower bound
    /// and exclusive upper bound `[low, high)`.
    /// Panics if `low >= high`.
    fn sample_single<R: Rng+?Sized>(low: Self::X, high: Self::X, rng: &mut R)
        -> Self::X
    {
        let range: Self = RangeImpl::new(low, high);
        range.sample(rng)
    }
}

/// Implementation of `RangeImpl` for integer types.
#[derive(Clone, Copy, Debug)]
pub struct RangeInt<X> {
    low: X,
    range: X,
    zone: X,
}

macro_rules! range_int_impl {
    ($ty:ty, $signed:ident, $unsigned:ident,
     $i_large:ident, $u_large:ident, $use_mult:expr) => {
        impl SampleRange for $ty {
            type T = RangeInt<$ty>;
        }

        impl RangeImpl for RangeInt<$ty> {
            // We play free and fast with unsigned vs signed here
            // (when $ty is signed), but that's fine, since the
            // contract of this macro is for $ty and $unsigned to be
            // "bit-equal", so casting between them is a no-op.

            type X = $ty;

            fn new(low: Self::X, high: Self::X) -> Self {
                RangeImpl::new_inclusive(low, high - 1)
            }

            fn new_inclusive(low: Self::X, high: Self::X) -> Self {
                // For a closed range the number of possible numbers we should
                // generate is `range = (high - low + 1)`. It is not possible to
                // end up with a uniform distribution if we map _all_ the random
                // integers that can be generated to this range. We have to map
                // integers from a `zone` that is a multiple of the range. The
                // rest of the integers, that cause a bias, are rejected. The
                // sampled number is `zone % range`.
                //
                // The problem with `range` is that to cover the full range of
                // the type, it has to store `unsigned_max + 1`, which can't be
                // represented. But if the range covers the full range of the
                // type, no modulus is needed. A range of size 0 can't exist, so
                // we use that to represent this special case. Wrapping
                // arithmetic even makes representing `unsigned_max + 1` as 0
                // simple.
                //
                // We don't calculate zone directly, but first calculate the
                // number of integers to reject. To handle `unsigned_max + 1`
                // not fitting in the type, we use:
                // ints_to_reject = (unsigned_max + 1) % range;
                // ints_to_reject = (unsigned_max - range + 1) % range;
                //
                // The smallest integer prngs generate is u32. That is why for
                // small integer sizes (i8/u8 and i16/u16) there is an
                // optimisation: don't pick the largest zone that can fit in the
                // small type, but pick the largest zone that can fit in an u32.
                // This improves the chance to get a random integer that fits in
                // the zone to 998 in 1000 in the worst case.
                //
                // There is a problem however: we can't store such a large range
                // in `RangeInt`, that can only hold values of the size of $ty.
                // `ints_to_reject` is always less than half the size of the
                // small integer. For an u8 it only ever uses 7 bits. This means
                // that all but the last 7 bits of `zone` are always 1's (or 15
                // in the case of u16). So nothing is lost by trucating `zone`.
                //
                // An alternative to using a modulus is widening multiply:
                // After a widening multiply by `range`, the result is in the
                // high word. Then comparing the low word against `zone` makes
                // sure our distribution is uniform.
                //
                // FIXME: This method is not used for i128/u128. It will
                // probably help a lot for performance, because a 128-bit
                // modulus is terribly slow. It means hand-coding a big-integer
                // widening multiply.

                let unsigned_max: $u_large = ::core::$u_large::MAX;

                let range = (high as $u_large)
                            .wrapping_sub(low as $u_large)
                            .wrapping_add(1);
                let ints_to_reject =
                    if range > 0 {
                        (unsigned_max - range + 1) % range
                    } else {
                        0
                    };
                let zone = unsigned_max - ints_to_reject;

                RangeInt {
                    low: low,
                    // These are really $unsigned values, but store as $ty:
                    range: range as $ty,
                    zone: zone as $ty
                }
            }

            fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> Self::X {
                let range = self.range as $unsigned as $u_large;
                if range > 0 {
                    // Some casting to recover the trucated bits of `zone`:
                    // First bit-cast to a signed int. Next sign-extend to the
                    // larger type. Then bit-cast to unsigned.
                    // For types that already have the right size, all the
                    // casting is a no-op.
                    let zone = self.zone as $signed as $i_large as $u_large;
                    loop {
                        let v: $u_large = Rand::rand(rng, Uniform);
                        if $use_mult {
                            let (hi, lo) = v.wmul(range);
                            if lo <= zone {
                                return self.low.wrapping_add(hi as $ty);
                            }
                        } else {
                            if v <= zone {
                                return self.low.wrapping_add((v % range) as $ty);
                            }
                        }
                    }
                } else {
                    // Sample from the entire integer range.
                    Rand::rand(rng, Uniform)
                }
            }

            fn sample_single<R: Rng+?Sized>(low: Self::X, high: Self::X, rng: &mut R) -> Self::X {
                let range = (high as $u_large)
                            .wrapping_sub(low as $u_large);
                let zone =
                    if ::core::$unsigned::MAX <= ::core::u16::MAX as $unsigned {
                        // Using a modulus is faster than the approximation for
                        // i8 and i16. I suppose we trade the cost of one
                        // modulus for near-perfect branch prediction.
                        let unsigned_max: $u_large = ::core::$u_large::MAX;
                        let ints_to_reject = (unsigned_max - range + 1) % range;
                        unsigned_max - ints_to_reject
                    } else {
                        // conservative but fast approximation
                       range << range.leading_zeros()
                    };

                loop {
                    let v: $u_large = Rand::rand(rng, Uniform);
                    if $use_mult {
                        let (hi, lo) = v.wmul(range);
                        if lo <= zone {
                            return low.wrapping_add(hi as $ty);
                        }
                    } else {
                        if v <= zone {
                            return low.wrapping_add((v % range) as $ty);
                        }
                    }
                }
            }
        }
    }
}

range_int_impl! { i8, i8, u8, i32, u32, true }
range_int_impl! { i16, i16, u16, i32, u32, true }
range_int_impl! { i32, i32, u32, i32, u32, true }
range_int_impl! { i64, i64, u64, i64, u64, true }
#[cfg(feature = "i128_support")]
range_int_impl! { i128, i128, u128, u128, u128, false }
range_int_impl! { isize, isize, usize, isize, usize, true }
range_int_impl! { u8, i8, u8, i32, u32, true }
range_int_impl! { u16, i16, u16, i32, u32, true }
range_int_impl! { u32, i32, u32, i32, u32, true }
range_int_impl! { u64, i64, u64, i64, u64, true }
range_int_impl! { usize, isize, usize, isize, usize, true }
#[cfg(feature = "i128_support")]
range_int_impl! { u128, u128, u128, i128, u128, false }


trait WideningMultiply<RHS = Self> {
    type Output;

    fn wmul(self, x: RHS) -> Self::Output;
}

macro_rules! wmul_impl {
    ($ty:ty, $wide:ident, $shift:expr) => {
        impl WideningMultiply for $ty {
            type Output = ($ty, $ty);

            #[inline(always)]
            fn wmul(self, x: $ty) -> Self::Output {
                let tmp = (self as $wide) * (x as $wide);
                ((tmp >> $shift) as $ty, tmp as $ty)
            }
        }
    }
}

wmul_impl! { u8, u16, 8 }
wmul_impl! { u16, u32, 16 }
wmul_impl! { u32, u64, 32 }

#[cfg(feature = "i128_support")]
wmul_impl! { u64, u128, 64 }

#[cfg(not(feature = "i128_support"))]
impl WideningMultiply for u64 {
    type Output = (u64, u64);

    // This code is a translation of the __mulddi3 function in LLVM's
    // compiler-rt. It is an optimised variant of the common method
    // `(a + b) * (c + d) = ac + ad + bc + bd`.
    //
    // For some reason LLVM can optimise the C version very well, but keeps
    // shuffeling registers in this Rust translation.
    #[inline(always)]
    fn wmul(self, b: u64) -> Self::Output {
        const LOWER_MASK: u64 = !0u64 >> 32;
        let mut low = (self & LOWER_MASK).wrapping_mul(b & LOWER_MASK);
        let mut t = low >> 32;
        low &= LOWER_MASK;
        t += (self >> 32).wrapping_mul(b & LOWER_MASK);
        low += (t & LOWER_MASK) << 32;
        let mut high = (t >> 32) as i64;
        t = low >> 32;
        low &= LOWER_MASK;
        t += (b >> 32).wrapping_mul(self & LOWER_MASK);
        low += (t & LOWER_MASK) << 32;
        high += (t >> 32) as i64;
        high += (self >> 32).wrapping_mul(b >> 32) as i64;

        (high as u64, low)
    }
}


macro_rules! wmul_impl_usize {
    ($ty:ty) => {
        impl WideningMultiply for usize {
            type Output = (usize, usize);

            #[inline(always)]
            fn wmul(self, x: usize) -> Self::Output {
                let (high, low) = (self as $ty).wmul(x as $ty);
                (high as usize, low as usize)
            }
        }
    }
}

#[cfg(target_pointer_width = "32")]
wmul_impl_usize! { u32 }
#[cfg(target_pointer_width = "64")]
wmul_impl_usize! { u64 }

#[cfg(feature = "i128_support")]
macro_rules! wmul_impl_128 {
    ($ty:ty) => {
        impl WideningMultiply for $ty {
            type Output = ($ty, $ty);

            #[inline(always)]
            fn wmul(self, _: $ty) -> Self::Output {
                unimplemented!();
            }
        }
    }
}

#[cfg(feature = "i128_support")]
wmul_impl_128! { i128 }
#[cfg(feature = "i128_support")]
wmul_impl_128! { u128 }



/// Implementation of `RangeImpl` for float types.
#[derive(Clone, Copy, Debug)]
pub enum RangeFloat<X> {
    // A range that is completely positive
    #[doc(hidden)]
    Positive { offset: X, scale: X },
    // A range that is completely negative
    #[doc(hidden)]
    Negative { offset: X, scale: X },
    // A range that is goes from negative to positive, but has more positive
    // than negative numbers
    #[doc(hidden)]
    PosAndNeg { cutoff: X, scale: X },
    // A range that is goes from negative to positive, but has more negative
    // than positive numbers
    #[doc(hidden)]
    NegAndPos { cutoff: X, scale: X },
}

macro_rules! range_float_impl {
    ($ty:ty, $next_u:path) => {
        impl SampleRange for $ty {
            type T = RangeFloat<$ty>;
        }

        impl RangeImpl for RangeFloat<$ty> {
            // We can distinguish between two different kinds of ranges:
            //
            // Completely positive or negative.
            // A characteristic of these ranges is that they get more bits of
            // precision as they get closer to 0.0. For positive ranges it is as
            // simple as applying a scale and offset to get the right range.
            // For a negative range, we apply a negative scale to transform the
            // range [0,1) to (-x,0]. Because this results in a range with it
            // closed and open sides reversed, we do not sample from
            // `closed_open01` but from `open_closed01`.
            //
            // A range that is both negative and positive.
            // This range has as characteristic that it does not have most of
            // its bits of precision near its low or high end, but in the middle
            // near 0.0. As the basis we use the [-1,1) range from
            // `closed_open11`.
            // How it works is easiest to explain with an example.
            // Suppose we want to sample from the range [-20, 100). We are
            // first going to scale the range from [-1,1) to (-60,60]. Note the
            // range changes from closed-open to open-closed because the scale
            // is negative.
            // If the sample happens to fall in the part (-60,-20), move it to
            // (-100,60). Then multiply by -1.
            // Scaling keeps the bits of precision intact. Moving the assymetric
            // part also does not waste precision, as the more you move away
            // from zero the less precision can be stored.

            type X = $ty;

            fn new(low: Self::X, high: Self::X) -> Self {
                if low >= 0.0 {
                    RangeFloat::Positive {
                        offset: low,
                        scale: high - low,
                    }
                } else if high <= 0.0 {
                    RangeFloat::Negative {
                        offset: high,
                        scale: low - high,
                    }
                } else if -low <= high {
                    RangeFloat::PosAndNeg {
                        cutoff: low,
                        scale: (high + low) / -2.0 + low,
                    }
                } else {
                    RangeFloat::NegAndPos {
                        cutoff: high,
                        scale: (high + low) / 2.0 - high,
                    }
                }
            }

            fn new_inclusive(low: Self::X, high: Self::X) -> Self {
                // Same as `new`, because the boundaries of a floats range are
                // (at least currently) not exact due to rounding errors.
                RangeImpl::new(low, high)
            }

            fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> Self::X {
                let rnd = $next_u(rng);
                match *self {
                    RangeFloat::Positive { offset, scale } => {
                        let x: $ty = rnd.closed_open01();
                        offset + scale * x
                    }
                    RangeFloat::Negative { offset, scale } => {
                        let x: $ty = rnd.open_closed01();
                        offset + scale * x
                    }
                    RangeFloat::PosAndNeg { cutoff, scale } => {
                        let x: $ty = rnd.closed_open11();
                        let x = x * scale;
                        if x < cutoff {
                            (cutoff - scale) - x
                        } else {
                            x
                        }
                    }
                    RangeFloat::NegAndPos { cutoff, scale } => {
                        let x: $ty = rnd.closed_open11();
                        let x = x * scale;
                        if x >= cutoff {
                            (cutoff + scale) - x
                        } else {
                            x
                        }
                    }
                }
            }
        }
    }
}

range_float_impl! { f32, Rng::next_u32 }
range_float_impl! { f64, Rng::next_u64 }

#[cfg(test)]
mod tests {
    use {Rng, thread_rng};
    use distributions::{Rand, Distribution};
    use distributions::range::{Range, RangeImpl, RangeFloat, SampleRange};

    #[test]
    fn test_fn_range() {
        let mut r = thread_rng();
        for _ in 0..1000 {
            let a = Range::new(-3, 42).sample(&mut r);
            assert!(a >= -3 && a < 42);
            assert_eq!(Range::new(0, 1).sample(&mut r), 0);
            assert_eq!(Range::new(-12, -11).sample(&mut r), -12);
        }

        for _ in 0..1000 {
            let a = Range::new(10, 42).sample(&mut r);
            assert!(a >= 10 && a < 42);
            assert_eq!(Range::new(0, 1).sample(&mut r), 0);
            assert_eq!(Range::new(3_000_000, 3_000_001).sample(&mut r), 3_000_000);
        }
    }

    #[test]
    #[should_panic]
    fn test_fn_range_panic_int() {
        let mut r = thread_rng();
        Range::new(5, -2).sample(&mut r);
    }

    #[test]
    #[should_panic]
    fn test_fn_range_panic_usize() {
        let mut r = thread_rng();
        Range::new(5, 2).sample(&mut r);
    }

    #[should_panic]
    #[test]
    fn test_range_bad_limits_equal() {
        Range::new(10, 10);
    }
    #[should_panic]
    #[test]
    fn test_range_bad_limits_flipped() {
        Range::new(10, 5);
    }

    #[test]
    fn test_integers() {
        let mut rng = ::test::rng();
        macro_rules! t {
            ($($ty:ident),*) => {{
                $(
                   let v: &[($ty, $ty)] = &[(0, 10),
                                            (10, 127),
                                            (::std::$ty::MIN, ::std::$ty::MAX)];
                   for &(low, high) in v.iter() {
                        let my_range = Range::new(low, high);
                        for _ in 0..1000 {
                            let v: $ty = Rand::rand(&mut rng, my_range);
                            assert!(low <= v && v < high);
                        }
                    }
                 )*
            }}
        }
        t!(i8, i16, i32, i64, isize,
           u8, u16, u32, u64, usize);
        #[cfg(feature = "i128_support")]
        t!(i128, u128)
    }

    #[test]
    fn test_floats() {
        let mut rng = ::test::rng();
        macro_rules! t {
            ($($ty:ty),*) => {{
                $(
                   let v: &[($ty, $ty)] = &[(0.0, 100.0),
                                            (-1e35, -1e25),
                                            (1e-35, 1e-25),
                                            (-1e35, 1e35)];
                   for &(low, high) in v.iter() {
                        let my_range = Range::new(low, high);
                        for _ in 0..1000 {
                            let v: $ty = Rand::rand(&mut rng, my_range);
                            assert!(low <= v && v < high);
                        }
                    }
                 )*
            }}
        }

        t!(f32, f64)
    }

    #[test]
    fn test_custom_range() {
        #[derive(Clone, Copy, PartialEq, PartialOrd)]
        struct MyF32 {
            x: f32,
        }
        #[derive(Clone, Copy, Debug)]
        struct RangeMyF32 {
            inner: RangeFloat<f32>,
        }
        impl RangeImpl for RangeMyF32 {
            type X = MyF32;
            fn new(low: Self::X, high: Self::X) -> Self {
                RangeMyF32 {
                    inner: RangeFloat::<f32>::new(low.x, high.x),
                }
            }
            fn new_inclusive(low: Self::X, high: Self::X) -> Self {
                RangeImpl::new(low, high)
            }
            fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> Self::X {
                MyF32 { x: self.inner.sample(rng) }
            }
        }
        impl SampleRange for MyF32 {
            type T = RangeMyF32;
        }

        let (low, high) = (MyF32{ x: 17.0f32 }, MyF32{ x: 22.0f32 });
        let range = Range::new(low, high);
        let mut rng = ::test::rng();
        for _ in 0..100 {
            let x = MyF32::rand(&mut rng, range);
            assert!(low <= x && x < high);
        }
    }
}
