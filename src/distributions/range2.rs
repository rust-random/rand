// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Alternative design for `Range`.
//! 
//! TODO: decide whether to replace the old `range` module with this.
//! Advantage: float ranges don't have to store a "zone" parameter.
//! Advantage: custom implementations can store extra parameters.
//! Possible advantage: easier implementations for custom types written in
//! terms of implementations of other types.
//! Disadvantage: complex?
//! 
//! This is *almost* like having separate `RangeInt<T>`, `RangeFloat<T>`,
//! etc. (or just `RangeI32`, etc.) types, each implementing `Distribution`,
//! but it adds some magic to support generic `range` and `new_range` methods.

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
/// use rand::distributions::range2::range;
///
/// let mut rng = rand::thread_rng();
/// let n: u32 = range(0, 10, &mut rng);
/// println!("{}", n);
/// let m: f64 = range(-40.0f64, 1.3e5f64, &mut rng);
/// println!("{}", m);
/// ```
pub fn range<X: SampleRange, R: Rng+?Sized>(low: X, high: X, rng: &mut R) -> X {
    assert!(low < high, "distributions::range called with low >= high");
    Range { inner: X::T::new(low, high) }.sample(rng)
}

/// Convenience function to construct a `Range`
pub fn new_range<X: SampleRange>(low: X, high: X) -> Range<X::T> {
    assert!(low < high, "new_range called with `low >= high`");
    Range { inner: RangeImpl::new(low, high) }
}

/// Sample values uniformly between two bounds.
///
/// This gives a uniform distribution (assuming the RNG used to sample
/// it is itself uniform & the `RangeImpl` implementation is correct),
/// even for edge cases like `low = 0u8`,
/// `high = 170u8`, for which a naive modulo operation would return
/// numbers less than 85 with double the probability to those greater
/// than 85.
///
/// Types should attempt to sample in `[low, high)`, i.e., not
/// including `high`, but this may be very difficult. All the
/// primitive integer types satisfy this property, and the float types
/// normally satisfy it, but rounding may mean `high` can occur.
/// 
/// # Example
///
/// ```rust
/// use rand::distributions::Distribution;
/// use rand::distributions::range2::new_range;
///
/// fn main() {
///     let between = new_range(10, 10000);
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

impl<T: RangeImpl> Range<T> {
    /// Create a new `Range` instance that samples uniformly from
    /// `[low, high)`. Panics if `low >= high`.
    pub fn new(low: T::X, high: T::X) -> Range<T> {
        assert!(low < high, "Range::new called with `low >= high`");
        Range { inner: RangeImpl::new(low, high) }
    }
}

impl<T: RangeImpl> Distribution<T::X> for Range<T> {
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> T::X {
        self.inner.sample(rng)
    }
}

/// Helper trait for creating implementations of `RangeImpl`.
pub trait SampleRange: PartialOrd+Sized {
    type T: RangeImpl<X = Self>;
}

/// Helper trait handling actual range sampling.
pub trait RangeImpl {
    /// The type sampled by this implementation.
    type X: PartialOrd;
    
    /// Construct self.
    /// 
    /// This should not be called directly. `Range::new` asserts that
    /// `low < high` before calling this.
    fn new(low: Self::X, high: Self::X) -> Self;
    
    /// Sample a value.
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> Self::X;
}

/// Implementation of `RangeImpl` for integer types.
#[derive(Clone, Copy, Debug)]
pub struct RangeInt<X> {
    low: X,
    range: X,
    zone: X,
}

macro_rules! range_int_impl {
    ($ty:ty, $unsigned:ident) => {
        impl SampleRange for $ty {
            type T = RangeInt<$ty>;
        }
        
        impl RangeImpl for RangeInt<$ty> {
            // we play free and fast with unsigned vs signed here
            // (when $ty is signed), but that's fine, since the
            // contract of this macro is for $ty and $unsigned to be
            // "bit-equal", so casting between them is a no-op & a
            // bijection.

            type X = $ty;
            
            fn new(low: Self::X, high: Self::X) -> Self {
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

                RangeInt {
                    low: low,
                    // These are really $unsigned values, but store as $ty:
                    range: range as $ty,
                    zone: zone as $ty
                }
            }
            
            fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> Self::X {
                use $crate::distributions::uniform;
                loop {
                    let v: $unsigned = uniform(rng);
                    // Reject samples not between 0 and zone:
                    if v <= self.zone as $unsigned {
                        // Adjustment sample for range and low value:
                        return (w(self.low) + w((v % self.range as $unsigned) as $ty)).0;
                    }
                }
            }
        }
    }
}

range_int_impl! { i8, u8 }
range_int_impl! { i16, u16 }
range_int_impl! { i32, u32 }
range_int_impl! { i64, u64 }
range_int_impl! { isize, usize }
range_int_impl! { u8, u8 }
range_int_impl! { u16, u16 }
range_int_impl! { u32, u32 }
range_int_impl! { u64, u64 }
range_int_impl! { usize, usize }

/// Implementation of `RangeImpl` for float types.
#[derive(Clone, Copy, Debug)]
pub struct RangeFloat<X> {
    low: X,
    range: X,
}

macro_rules! range_float_impl {
    ($ty:ty) => {
        impl SampleRange for $ty {
            type T = RangeFloat<$ty>;
        }
        
        impl RangeImpl for RangeFloat<$ty> {
            type X = $ty;
            
            fn new(low: Self::X, high: Self::X) -> Self {
                RangeFloat {
                    low: low,
                    range: high - low,
                }
            }
            
            fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> Self::X {
                let x: $ty = Rand::rand(rng, Uniform01);
                self.low + self.range * x
            }
        }
    }
}

range_float_impl! { f32 }
range_float_impl! { f64 }

#[cfg(test)]
mod tests {
    use {Rng, thread_rng};
    use distributions::Rand;
    use distributions::range2::{Range, range, new_range, RangeImpl, RangeFloat};

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
        new_range(10, 10);
    }
    #[should_panic]
    #[test]
    fn test_range_bad_limits_flipped() {
        new_range(10, 5);
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
                        let range = new_range(low, high);
                        for _ in 0..1000 {
                            let v: $ty = Rand::rand(&mut rng, range);
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
                        let range = new_range(low, high);
                        for _ in 0..1000 {
                            let v: $ty = Rand::rand(&mut rng, range);
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
            fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> Self::X {
                MyF32 { x: self.inner.sample(rng) }
            }
        }
        
        let (low, high) = (MyF32{ x: 17.0f32 }, MyF32{ x: 22.0f32 });
        let range = Range::<RangeMyF32>::new(low, high);
        let mut rng = ::test::rng();
        for _ in 0..100 {
            let x = MyF32::rand(&mut rng, range);
            assert!(low <= x && x < high);
        }
    }
}
