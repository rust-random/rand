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

use core::num::Int;
use core::ops::Range;

use Rng;
use distributions::{Sample, IndependentSample};

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
/// # Example
///
/// ```rust
/// use rand::distributions::IndependentSample;
///
/// fn main() {
///     let between = 10..10000;
///     let mut rng = rand::thread_rng();
///     let mut sum = 0;
///     for _ in 0..1000 {
///         sum += between.ind_sample(&mut rng);
///     }
///     println!("{}", sum);
/// }
/// ```

impl<Sup: SampleRange> Sample<Sup> for Range<Sup> {
    #[inline]
    fn sample<R: Rng>(&mut self, rng: &mut R) -> Sup { self.ind_sample(rng) }
}
impl<Sup: SampleRange> IndependentSample<Sup> for Range<Sup> {
    fn ind_sample<R: Rng>(&self, rng: &mut R) -> Sup {
        SampleRange::sample_range(self, rng)
    }
}

/// The helper trait for types that have a sensible way to sample
/// uniformly between two values. This should not be used directly,
/// and is only to facilitate `Range`.
pub trait SampleRange {

    /// Sample a value from the given `Range` with the given `Rng` as
    /// a source of randomness.
    fn sample_range<R: Rng>(r: &Range<Self>, rng: &mut R) -> Self;
}

macro_rules! integer_impl {
    ($ty:ty, $unsigned:ty) => {
        impl SampleRange for $ty {
            // we play free and fast with unsigned vs signed here
            // (when $ty is signed), but that's fine, since the
            // contract of this macro is for $ty and $unsigned to be
            // "bit-equal", so casting between them is a no-op & a
            // bijection.

            #[inline]
            fn sample_range<R: Rng>(r: &Range<$ty>, rng: &mut R) -> $ty {
                assert!(r.start < r.end, "Rng.sample_range called with low >= high");
                let range = r.end as $unsigned - r.start as $unsigned;
                let unsigned_max: $unsigned = Int::max_value();

                // this is the largest number that fits into $unsigned
                // that `range` divides evenly, so, if we've sampled
                // `n` uniformly from this region, then `n % range` is
                // uniform in [0, range)
                let zone = unsigned_max - unsigned_max % range;
                loop {
                    // rejection sample
                    let v = rng.gen::<$unsigned>();
                    // until we find something that fits into the
                    // region which r.range evenly divides (this will
                    // be uniformly distributed)
                    if v < zone {
                        // and return it, with some adjustments
                        return r.start + (v % range as $unsigned) as $ty;
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
            #[inline]
            fn sample_range<R: Rng>(r: &Range<$ty>, rng: &mut R) -> $ty {
                assert!(r.start < r.end, "Rng.gen_range called with low >= high");
                r.start + (r.end - r.start) * rng.gen()
            }
        }
    }
}

float_impl! { f32 }
float_impl! { f64 }

#[cfg(test)]
mod tests {
    use std::num::Int;
    use std::prelude::v1::*;
    use distributions::{Sample, IndependentSample};

    #[should_fail]
    #[test]
    fn test_range_bad_limits_equal() {
        let mut rng = ::test::rng();
        (10..10).sample(&mut rng);
    }
    #[should_fail]
    #[test]
    fn test_range_bad_limits_flipped() {
        let mut rng = ::test::rng();
        (10..5).sample(&mut rng);
    }

    #[test]
    fn test_integers() {
        let mut rng = ::test::rng();
        macro_rules! t {
            ($($ty:ty),*) => {{
                $(
                   let v: &[($ty, $ty)] = &[(0, 10),
                                            (10, 127),
                                            (Int::min_value(), Int::max_value())];
                   for &(low, high) in v.iter() {
                        for _ in 0..1000 {
                            let v = (low..high).sample(&mut rng);
                            assert!(low <= v && v < high);
                            let v = (low..high).ind_sample(&mut rng);
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
                        for _ in 0..1000 {
                            let v = (low..high).sample(&mut rng);
                            assert!(low <= v && v < high);
                            let v = (low..high).ind_sample(&mut rng);
                            assert!(low <= v && v < high);
                        }
                    }
                 )*
            }}
        }

        t!(f32, f64)
    }

}

#[cfg(test)]
mod bench {
    extern crate test;
    use std::prelude::v1::*;
    use self::test::Bencher;
    use std::mem::size_of;
    use distributions::IndependentSample;

    #[bench]
    fn rand_float(b: &mut Bencher) {
        let mut rng = ::test::weak_rng();
        let range = -2.71828..3.14159;

        b.iter(|| {
            for _ in 0..::RAND_BENCH_N {
                range.ind_sample(&mut rng);
            }
        });
        b.bytes = size_of::<f64>() as u64 * ::RAND_BENCH_N;
    }

    #[bench]
    fn rand_int(b: &mut Bencher) {
        let mut rng = ::test::weak_rng();
        let range = -99..6418i32;

        b.iter(|| {
            for _ in 0..::RAND_BENCH_N {
                range.ind_sample(&mut rng);
            }
        });
        b.bytes = size_of::<f64>() as u64 * ::RAND_BENCH_N;
    }
}
