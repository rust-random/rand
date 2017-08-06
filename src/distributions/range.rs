// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Generating numbers between two others.

// this is surprisingly complicated to be both generic & correct

use core::num::Wrapping as w;

use Rng;
use distributions::{Distribution, Uniform01, Rand};

/// Generate a random value in the range [`low`, `high`).
///
/// This is a convenience wrapper around `Range`. If this function will be called
/// repeatedly with the same arguments, one should use `Range`, as that will
/// amortize the computations that allow for perfect uniformity.
///
/// # Panics
///
/// Panics if `low >= high`.
///
/// # Example
///
/// ```rust
/// use rand::distributions::range;
///
/// let mut rng = rand::thread_rng();
/// let n: u32 = range(0, 10, &mut rng);
/// println!("{}", n);
/// let m: f64 = range(-40.0f64, 1.3e5f64, &mut rng);
/// println!("{}", m);
/// ```
pub fn range<T: SampleRange, R: Rng+?Sized>(low: T, high: T, rng: &mut R) -> T {
    assert!(low < high, "distributions::range called with low >= high");
    SampleRange::construct_range(low, high).sample(rng)
}

/// Sample values uniformly between two bounds.
///
/// This gives a uniform distribution (assuming the RNG used to sample
/// it is itself uniform & the `SampleRange` implementation for the
/// given type is correct), even for edge cases like `low = 0u8`,
/// `high = 170u8`, for which a naive modulo operation would return
/// numbers less than 85 with double the probability to those greater
/// than 85.
///
/// Types should attempt to sample in `[low, high)`, i.e., not
/// including `high`, but this may be very difficult. All the
/// primitive integer types satisfy this property, and the float types
/// normally satisfy it, but rounding may mean `high` can occur.
/// 
/// Internal details of this type are exposed so as to allow users to implement
/// `SampleRange` for their own types. Outside of `SampleRange` implementations,
/// accessing these members should not be necessary.
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
pub struct Range<X> {
    /// The `low` of `Range::new(low, high)`.
    pub low: X,
    /// Usually it is more convenient to store `low` and `range = high - low`
    /// internally. Custom implementations of `SampleRange` may however use
    /// this differently.
    pub range: X,
    /// The integer implementation ensures uniform distribution by rejecting
    /// parameters outside of a certain "acceptance zone", from `0` to `zone`.
    /// Not all implementations use this parameter.
    pub zone: X
}

impl<X: SampleRange> Range<X> {
    /// Create a new `Range` instance that samples uniformly from
    /// `[low, high)`. Panics if `low >= high`.
    pub fn new(low: X, high: X) -> Range<X> {
        assert!(low < high, "Range::new called with `low >= high`");
        SampleRange::construct_range(low, high)
    }
}

impl<T: SampleRange> Distribution<T> for Range<T> {
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> T {
        SampleRange::sample_range(self, rng)
    }
}

/// The helper trait for types that have a sensible way to sample
/// uniformly between two values. This should not be used directly,
/// and is only to facilitate `Range`.
pub trait SampleRange : PartialOrd+Sized {
    /// Construct the `Range` object that `sample_range`
    /// requires. This should not ever be called directly, only via
    /// `Range::new`, which will check that `low < high`, so this
    /// function doesn't have to repeat the check.
    fn construct_range(low: Self, high: Self) -> Range<Self>;

    /// Sample a value from the given `Range` with the given `Rng` as
    /// a source of randomness.
    fn sample_range<R: Rng+?Sized>(r: &Range<Self>, rng: &mut R) -> Self;
}

macro_rules! integer_impl {
    ($ty:ty, $unsigned:ident) => {
        impl SampleRange for $ty {
            // we play free and fast with unsigned vs signed here
            // (when $ty is signed), but that's fine, since the
            // contract of this macro is for $ty and $unsigned to be
            // "bit-equal", so casting between them is a no-op & a
            // bijection.

            #[inline]
            fn construct_range(low: $ty, high: $ty) -> Range<$ty> {
                let range = (w(high as $unsigned) - w(low as $unsigned)).0;
                let unsigned_max: $unsigned = ::core::$unsigned::MAX;

                // We want to calculate type_range % range where type_range is
                // pow(2, n_bits($ty)), but we can't represent type_range.
                // (type_range - range) % range is equivalent, since we know
                // type_range > range. Since range >= 1,
                // type_range - range = (unsigned_max - range) + 1.
                let ignore_zone = ((unsigned_max - range) + 1) % range;
                // We want to sample from the zone
                // [0, (type_range - ignore_zone))
                // however, ignore_zone may be zero. Instead use a closed range
                // from zero to:
                let zone = unsigned_max - ignore_zone;

                Range {
                    low: low,
                    // These are really $unsigned values, but store as $ty:
                    range: range as $ty,
                    zone: zone as $ty
                }
            }

            #[inline]
            fn sample_range<R: Rng+?Sized>(r: &Range<$ty>, rng: &mut R) -> $ty {
                use $crate::distributions::uniform;
                loop {
                    let v: $unsigned = uniform(rng);
                    // Reject samples not between 0 and zone:
                    if v <= r.zone as $unsigned {
                        // Adjustment sample for range and low value:
                        return (w(r.low) + w((v % r.range as $unsigned) as $ty)).0;
                    }
                }
            }
        }
    }
}

integer_impl! { i8, u8 }
integer_impl! { i16, u16 }
integer_impl! { i32, u32 }
integer_impl! { i64, u64 }
integer_impl! { isize, usize }
integer_impl! { u8, u8 }
integer_impl! { u16, u16 }
integer_impl! { u32, u32 }
integer_impl! { u64, u64 }
integer_impl! { usize, usize }

macro_rules! float_impl {
    ($ty:ty) => {
        impl SampleRange for $ty {
            fn construct_range(low: $ty, high: $ty) -> Range<$ty> {
                Range {
                    low: low,
                    range: high - low,
                    zone: 0.0 // unused
                }
            }
            fn sample_range<R: Rng+?Sized>(r: &Range<$ty>, rng: &mut R) -> $ty {
                let x: $ty = Rand::rand(rng, Uniform01);
                r.low + r.range * x
            }
        }
    }
}

float_impl! { f32 }
float_impl! { f64 }

#[cfg(test)]
mod tests {
    use {Rng, thread_rng};
    use distributions::{Distribution, Rand, Uniform01};
    use distributions::range::{Range, range, SampleRange};

    #[test]
    fn test_fn_range() {
        let mut r = thread_rng();
        for _ in 0..1000 {
            let a = range(-3, 42, &mut r);
            assert!(a >= -3 && a < 42);
            assert_eq!(range(0, 1, &mut r), 0);
            assert_eq!(range(-12, -11, &mut r), -12);
        }

        for _ in 0..1000 {
            let a = range(10, 42, &mut r);
            assert!(a >= 10 && a < 42);
            assert_eq!(range(0, 1, &mut r), 0);
            assert_eq!(range(3_000_000, 3_000_001, &mut r), 3_000_000);
        }

    }
    
    #[test]
    #[should_panic]
    fn test_fn_range_panic_int() {
        let mut r = thread_rng();
        range(5, -2, &mut r);
    }

    #[test]
    #[should_panic]
    fn test_fn_range_panic_usize() {
        let mut r = thread_rng();
        range(5, 2, &mut r);
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
                        let sampler: Range<$ty> = Range::new(low, high);
                        for _ in 0..1000 {
                            let v = sampler.sample(&mut rng);
                            assert!(low <= v && v < high);
                        }
                    }
                 )*
            }}
        }
        t!(i8, i16, i32, i64, isize,
           u8, u16, u32, u64, usize)
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
                        let sampler: Range<$ty> = Range::new(low, high);
                        for _ in 0..1000 {
                            let v = sampler.sample(&mut rng);
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
        impl SampleRange for MyF32 {
            fn construct_range(low: MyF32, high: MyF32) -> Range<MyF32> {
                Range {
                    low: low,
                    range: MyF32 { x: high.x - low.x },
                    zone: MyF32 { x: 0.0f32 }
                }
            }
            fn sample_range<R: Rng+?Sized>(r: &Range<MyF32>, rng: &mut R) -> MyF32 {
                let x = f32::rand(rng, Uniform01);
                MyF32 { x: r.low.x + r.range.x * x }
            }
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
