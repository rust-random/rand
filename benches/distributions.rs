// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(custom_inner_attributes)]
#![feature(test)]

// Rustfmt splits macro invocations to shorten lines; in this case longer-lines are more readable
#![rustfmt::skip]

extern crate test;

const RAND_BENCH_N: u64 = 1000;

use rand::distributions::{Alphanumeric, Open01, OpenClosed01, Standard, Uniform};
use rand::distributions::uniform::{UniformInt, UniformSampler};
use core::mem::size_of;
use core::num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8};
use core::time::Duration;
use test::{Bencher, black_box};

use rand::prelude::*;

// At this time, distributions are optimised for 64-bit platforms.
use rand_pcg::Pcg64Mcg;

macro_rules! distr_int {
    ($fnn:ident, $ty:ty, $distr:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = Pcg64Mcg::from_entropy();
            let distr = $distr;

            b.iter(|| {
                let mut accum = 0 as $ty;
                for _ in 0..RAND_BENCH_N {
                    let x: $ty = distr.sample(&mut rng);
                    accum = accum.wrapping_add(x);
                }
                accum
            });
            b.bytes = size_of::<$ty>() as u64 * RAND_BENCH_N;
        }
    };
}

macro_rules! distr_nz_int {
    ($fnn:ident, $tynz:ty, $ty:ty, $distr:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = Pcg64Mcg::from_entropy();
            let distr = $distr;

            b.iter(|| {
                let mut accum = 0 as $ty;
                for _ in 0..RAND_BENCH_N {
                    let x: $tynz = distr.sample(&mut rng);
                    accum = accum.wrapping_add(x.get());
                }
                accum
            });
            b.bytes = size_of::<$ty>() as u64 * RAND_BENCH_N;
        }
    };
}

macro_rules! distr_float {
    ($fnn:ident, $ty:ty, $distr:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = Pcg64Mcg::from_entropy();
            let distr = $distr;

            b.iter(|| {
                let mut accum = 0.0;
                for _ in 0..RAND_BENCH_N {
                    let x: $ty = distr.sample(&mut rng);
                    accum += x;
                }
                accum
            });
            b.bytes = size_of::<$ty>() as u64 * RAND_BENCH_N;
        }
    };
}

macro_rules! distr_duration {
    ($fnn:ident, $distr:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = Pcg64Mcg::from_entropy();
            let distr = $distr;

            b.iter(|| {
                let mut accum = Duration::new(0, 0);
                for _ in 0..RAND_BENCH_N {
                    let x: Duration = distr.sample(&mut rng);
                    accum = accum
                        .checked_add(x)
                        .unwrap_or(Duration::new(u64::max_value(), 999_999_999));
                }
                accum
            });
            b.bytes = size_of::<Duration>() as u64 * RAND_BENCH_N;
        }
    };
}

macro_rules! distr {
    ($fnn:ident, $ty:ty, $distr:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = Pcg64Mcg::from_entropy();
            let distr = $distr;

            b.iter(|| {
                let mut accum = 0u32;
                for _ in 0..RAND_BENCH_N {
                    let x: $ty = distr.sample(&mut rng);
                    accum = accum.wrapping_add(x as u32);
                }
                accum
            });
            b.bytes = size_of::<$ty>() as u64 * RAND_BENCH_N;
        }
    };
}

// uniform
distr_int!(distr_uniform_i8, i8, Uniform::new(20i8, 100));
distr_int!(distr_uniform_i16, i16, Uniform::new(-500i16, 2000));
distr_int!(distr_uniform_i32, i32, Uniform::new(-200_000_000i32, 800_000_000));
distr_int!(distr_uniform_i64, i64, Uniform::new(3i64, 123_456_789_123));
distr_int!(distr_uniform_i128, i128, Uniform::new(-123_456_789_123i128, 123_456_789_123_456_789));
distr_int!(distr_uniform_usize16, usize, Uniform::new(0usize, 0xb9d7));
distr_int!(distr_uniform_usize32, usize, Uniform::new(0usize, 0x548c0f43));
#[cfg(target_pointer_width = "64")]
distr_int!(distr_uniform_usize64, usize, Uniform::new(0usize, 0x3a42714f2bf927a8));
distr_int!(distr_uniform_isize, isize, Uniform::new(-1060478432isize, 1858574057));

distr_float!(distr_uniform_f32, f32, Uniform::new(2.26f32, 2.319));
distr_float!(distr_uniform_f64, f64, Uniform::new(2.26f64, 2.319));

const LARGE_SEC: u64 = u64::max_value() / 1000;

distr_duration!(distr_uniform_duration_largest,
    Uniform::new_inclusive(Duration::new(0, 0), Duration::new(u64::max_value(), 999_999_999))
);
distr_duration!(distr_uniform_duration_large,
    Uniform::new(Duration::new(0, 0), Duration::new(LARGE_SEC, 1_000_000_000 / 2))
);
distr_duration!(distr_uniform_duration_one,
    Uniform::new(Duration::new(0, 0), Duration::new(1, 0))
);
distr_duration!(distr_uniform_duration_variety,
    Uniform::new(Duration::new(10000, 423423), Duration::new(200000, 6969954))
);
distr_duration!(distr_uniform_duration_edge,
    Uniform::new_inclusive(Duration::new(LARGE_SEC, 999_999_999), Duration::new(LARGE_SEC + 1, 1))
);

// standard
distr_int!(distr_standard_i8, i8, Standard);
distr_int!(distr_standard_i16, i16, Standard);
distr_int!(distr_standard_i32, i32, Standard);
distr_int!(distr_standard_i64, i64, Standard);
distr_int!(distr_standard_i128, i128, Standard);
distr_nz_int!(distr_standard_nz8, NonZeroU8, u8, Standard);
distr_nz_int!(distr_standard_nz16, NonZeroU16, u16, Standard);
distr_nz_int!(distr_standard_nz32, NonZeroU32, u32, Standard);
distr_nz_int!(distr_standard_nz64, NonZeroU64, u64, Standard);
distr_nz_int!(distr_standard_nz128, NonZeroU128, u128, Standard);

distr!(distr_standard_bool, bool, Standard);
distr!(distr_standard_alphanumeric, u8, Alphanumeric);
distr!(distr_standard_codepoint, char, Standard);

distr_float!(distr_standard_f32, f32, Standard);
distr_float!(distr_standard_f64, f64, Standard);
distr_float!(distr_open01_f32, f32, Open01);
distr_float!(distr_open01_f64, f64, Open01);
distr_float!(distr_openclosed01_f32, f32, OpenClosed01);
distr_float!(distr_openclosed01_f64, f64, OpenClosed01);

// construct and sample from a range
macro_rules! gen_range_int {
    ($fnn:ident, $ty:ident, $low:expr, $high:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = Pcg64Mcg::from_entropy();

            b.iter(|| {
                let mut high = $high;
                let mut accum: $ty = 0;
                for _ in 0..RAND_BENCH_N {
                    accum = accum.wrapping_add(rng.gen_range($low..high));
                    // force recalculation of range each time
                    high = high.wrapping_add(1) & core::$ty::MAX;
                }
                accum
            });
            b.bytes = size_of::<$ty>() as u64 * RAND_BENCH_N;
        }
    };
}

// Algorithms such as Fisher–Yates shuffle often require uniform values from an
// incrementing range 0..n. We use -1..n here to prevent wrapping in the test 
// from generating a 0-sized range.
gen_range_int!(gen_range_i8_low, i8, -1i8, 0);
gen_range_int!(gen_range_i16_low, i16, -1i16, 0);
gen_range_int!(gen_range_i32_low, i32, -1i32, 0);
gen_range_int!(gen_range_i64_low, i64, -1i64, 0);
gen_range_int!(gen_range_i128_low, i128, -1i128, 0);

// These were the initially tested ranges. They are likely to see fewer
// rejections than the low tests.
gen_range_int!(gen_range_i8_high, i8, -20i8, 100);
gen_range_int!(gen_range_i16_high, i16, -500i16, 2000);
gen_range_int!(gen_range_i32_high, i32, -200_000_000i32, 800_000_000);
gen_range_int!(gen_range_i64_high, i64, 3i64, 123_456_789_123);
gen_range_int!(gen_range_i128_high, i128, -12345678901234i128, 123_456_789_123_456_789);

// construct and sample from a floating-point range
macro_rules! gen_range_float {
    ($fnn:ident, $ty:ident, $low:expr, $high:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = Pcg64Mcg::from_entropy();

            b.iter(|| {
                let mut high = $high;
                let mut low = $low;
                let mut accum: $ty = 0.0;
                for _ in 0..RAND_BENCH_N {
                    accum += rng.gen_range(low..high);
                    // force recalculation of range each time
                    low += 0.9;
                    high += 1.1;
                }
                accum
            });
            b.bytes = size_of::<$ty>() as u64 * RAND_BENCH_N;
        }
    };
}

gen_range_float!(gen_range_f32, f32, -20000.0f32, 100000.0);
gen_range_float!(gen_range_f64, f64, 123.456f64, 7890.12);


// In src/distributions/uniform.rs, we say:
// Implementation of [`uniform_single`] is optional, and is only useful when
// the implementation can be faster than `Self::new(low, high).sample(rng)`.

// `UniformSampler::uniform_single` compromises on the rejection range to be
// faster. This benchmark demonstrates both the speed gain of doing this, and
// the worst case behavior.

/// Sample random values from a pre-existing distribution.  This uses the
/// half open `new` to be equivalent to the behavior of `uniform_single`.
macro_rules! uniform_sample {
    ($fnn:ident, $type:ident, $low:expr, $high:expr, $count:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = Pcg64Mcg::from_entropy();
            let low = black_box($low);
            let high = black_box($high);
            b.iter(|| {
                for _ in 0..10 {
                    let dist = UniformInt::<$type>::new(low, high);
                    for _ in 0..$count {
                        black_box(dist.sample(&mut rng));
                    }
                }
            });
        }
    };
}

macro_rules! uniform_inclusive {
    ($fnn:ident, $type:ident, $low:expr, $high:expr, $count:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = Pcg64Mcg::from_entropy();
            let low = black_box($low);
            let high = black_box($high);
            b.iter(|| {
                for _ in 0..10 {
                    let dist = UniformInt::<$type>::new_inclusive(low, high);
                    for _ in 0..$count {
                        black_box(dist.sample(&mut rng));
                    }
                }
            });
        }
    };
}

/// Use `uniform_single` to create a one-off random value
macro_rules! uniform_single {
    ($fnn:ident, $type:ident, $low:expr, $high:expr, $count:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = Pcg64Mcg::from_entropy();
            let low = black_box($low);
            let high = black_box($high);
            b.iter(|| {
                for _ in 0..(10 * $count) {
                    black_box(UniformInt::<$type>::sample_single(low, high, &mut rng));
                }
            });
        }
    };
}


// Benchmark:
// n: can use the full generated range
// (n-1): only the max value is rejected: expect this to be fast
// n/2+1: almost half of the values are rejected, and we can do no better
// n/2: approximation rejects half the values but powers of 2 could have no rejection
// n/2-1: only a few values are rejected: expect this to be fast
// 6: approximation rejects 25% of values but could be faster. However modulo by
//    low numbers is typically more expensive

// With the use of u32 as the minimum generated width, the worst-case u16 range 
// (32769) will only reject 32769 / 4294967296 samples.
const HALF_16_BIT_UNSIGNED: u16 = 1 << 15;

uniform_sample!(uniform_u16x1_allm1_new, u16, 0, u16::max_value(), 1);
uniform_sample!(uniform_u16x1_halfp1_new, u16, 0, HALF_16_BIT_UNSIGNED + 1, 1);
uniform_sample!(uniform_u16x1_half_new, u16, 0, HALF_16_BIT_UNSIGNED, 1);
uniform_sample!(uniform_u16x1_halfm1_new, u16, 0, HALF_16_BIT_UNSIGNED - 1, 1);
uniform_sample!(uniform_u16x1_6_new, u16, 0, 6u16, 1);

uniform_single!(uniform_u16x1_allm1_single, u16, 0, u16::max_value(), 1);
uniform_single!(uniform_u16x1_halfp1_single, u16, 0, HALF_16_BIT_UNSIGNED + 1, 1);
uniform_single!(uniform_u16x1_half_single, u16, 0, HALF_16_BIT_UNSIGNED, 1);
uniform_single!(uniform_u16x1_halfm1_single, u16, 0, HALF_16_BIT_UNSIGNED - 1, 1);
uniform_single!(uniform_u16x1_6_single, u16, 0, 6u16, 1);

uniform_inclusive!(uniform_u16x10_all_new_inclusive, u16, 0, u16::max_value(), 10);
uniform_sample!(uniform_u16x10_allm1_new, u16, 0, u16::max_value(), 10);
uniform_sample!(uniform_u16x10_halfp1_new, u16, 0, HALF_16_BIT_UNSIGNED + 1, 10);
uniform_sample!(uniform_u16x10_half_new, u16, 0, HALF_16_BIT_UNSIGNED, 10);
uniform_sample!(uniform_u16x10_halfm1_new, u16, 0, HALF_16_BIT_UNSIGNED - 1, 10);
uniform_sample!(uniform_u16x10_6_new, u16, 0, 6u16, 10);

uniform_single!(uniform_u16x10_allm1_single, u16, 0, u16::max_value(), 10);
uniform_single!(uniform_u16x10_halfp1_single, u16, 0, HALF_16_BIT_UNSIGNED + 1, 10);
uniform_single!(uniform_u16x10_half_single, u16, 0, HALF_16_BIT_UNSIGNED, 10);
uniform_single!(uniform_u16x10_halfm1_single, u16, 0, HALF_16_BIT_UNSIGNED - 1, 10);
uniform_single!(uniform_u16x10_6_single, u16, 0, 6u16, 10);


const HALF_32_BIT_UNSIGNED: u32 = 1 << 31;

uniform_sample!(uniform_u32x1_allm1_new, u32, 0, u32::max_value(), 1);
uniform_sample!(uniform_u32x1_halfp1_new, u32, 0, HALF_32_BIT_UNSIGNED + 1, 1);
uniform_sample!(uniform_u32x1_half_new, u32, 0, HALF_32_BIT_UNSIGNED, 1);
uniform_sample!(uniform_u32x1_halfm1_new, u32, 0, HALF_32_BIT_UNSIGNED - 1, 1);
uniform_sample!(uniform_u32x1_6_new, u32, 0, 6u32, 1);

uniform_single!(uniform_u32x1_allm1_single, u32, 0, u32::max_value(), 1);
uniform_single!(uniform_u32x1_halfp1_single, u32, 0, HALF_32_BIT_UNSIGNED + 1, 1);
uniform_single!(uniform_u32x1_half_single, u32, 0, HALF_32_BIT_UNSIGNED, 1);
uniform_single!(uniform_u32x1_halfm1_single, u32, 0, HALF_32_BIT_UNSIGNED - 1, 1);
uniform_single!(uniform_u32x1_6_single, u32, 0, 6u32, 1);

uniform_inclusive!(uniform_u32x10_all_new_inclusive, u32, 0, u32::max_value(), 10);
uniform_sample!(uniform_u32x10_allm1_new, u32, 0, u32::max_value(), 10);
uniform_sample!(uniform_u32x10_halfp1_new, u32, 0, HALF_32_BIT_UNSIGNED + 1, 10);
uniform_sample!(uniform_u32x10_half_new, u32, 0, HALF_32_BIT_UNSIGNED, 10);
uniform_sample!(uniform_u32x10_halfm1_new, u32, 0, HALF_32_BIT_UNSIGNED - 1, 10);
uniform_sample!(uniform_u32x10_6_new, u32, 0, 6u32, 10);

uniform_single!(uniform_u32x10_allm1_single, u32, 0, u32::max_value(), 10);
uniform_single!(uniform_u32x10_halfp1_single, u32, 0, HALF_32_BIT_UNSIGNED + 1, 10);
uniform_single!(uniform_u32x10_half_single, u32, 0, HALF_32_BIT_UNSIGNED, 10);
uniform_single!(uniform_u32x10_halfm1_single, u32, 0, HALF_32_BIT_UNSIGNED - 1, 10);
uniform_single!(uniform_u32x10_6_single, u32, 0, 6u32, 10);

const HALF_64_BIT_UNSIGNED: u64 = 1 << 63;

uniform_sample!(uniform_u64x1_allm1_new, u64, 0, u64::max_value(), 1);
uniform_sample!(uniform_u64x1_halfp1_new, u64, 0, HALF_64_BIT_UNSIGNED + 1, 1);
uniform_sample!(uniform_u64x1_half_new, u64, 0, HALF_64_BIT_UNSIGNED, 1);
uniform_sample!(uniform_u64x1_halfm1_new, u64, 0, HALF_64_BIT_UNSIGNED - 1, 1);
uniform_sample!(uniform_u64x1_6_new, u64, 0, 6u64, 1);

uniform_single!(uniform_u64x1_allm1_single, u64, 0, u64::max_value(), 1);
uniform_single!(uniform_u64x1_halfp1_single, u64, 0, HALF_64_BIT_UNSIGNED + 1, 1);
uniform_single!(uniform_u64x1_half_single, u64, 0, HALF_64_BIT_UNSIGNED, 1);
uniform_single!(uniform_u64x1_halfm1_single, u64, 0, HALF_64_BIT_UNSIGNED - 1, 1);
uniform_single!(uniform_u64x1_6_single, u64, 0, 6u64, 1);

uniform_inclusive!(uniform_u64x10_all_new_inclusive, u64, 0, u64::max_value(), 10);
uniform_sample!(uniform_u64x10_allm1_new, u64, 0, u64::max_value(), 10);
uniform_sample!(uniform_u64x10_halfp1_new, u64, 0, HALF_64_BIT_UNSIGNED + 1, 10);
uniform_sample!(uniform_u64x10_half_new, u64, 0, HALF_64_BIT_UNSIGNED, 10);
uniform_sample!(uniform_u64x10_halfm1_new, u64, 0, HALF_64_BIT_UNSIGNED - 1, 10);
uniform_sample!(uniform_u64x10_6_new, u64, 0, 6u64, 10);

uniform_single!(uniform_u64x10_allm1_single, u64, 0, u64::max_value(), 10);
uniform_single!(uniform_u64x10_halfp1_single, u64, 0, HALF_64_BIT_UNSIGNED + 1, 10);
uniform_single!(uniform_u64x10_half_single, u64, 0, HALF_64_BIT_UNSIGNED, 10);
uniform_single!(uniform_u64x10_halfm1_single, u64, 0, HALF_64_BIT_UNSIGNED - 1, 10);
uniform_single!(uniform_u64x10_6_single, u64, 0, 6u64, 10);

const HALF_128_BIT_UNSIGNED: u128 = 1 << 127;

uniform_sample!(uniform_u128x1_allm1_new, u128, 0, u128::max_value(), 1);
uniform_sample!(uniform_u128x1_halfp1_new, u128, 0, HALF_128_BIT_UNSIGNED + 1, 1);
uniform_sample!(uniform_u128x1_half_new, u128, 0, HALF_128_BIT_UNSIGNED, 1);
uniform_sample!(uniform_u128x1_halfm1_new, u128, 0, HALF_128_BIT_UNSIGNED - 1, 1);
uniform_sample!(uniform_u128x1_6_new, u128, 0, 6u128, 1);

uniform_single!(uniform_u128x1_allm1_single, u128, 0, u128::max_value(), 1);
uniform_single!(uniform_u128x1_halfp1_single, u128, 0, HALF_128_BIT_UNSIGNED + 1, 1);
uniform_single!(uniform_u128x1_half_single, u128, 0, HALF_128_BIT_UNSIGNED, 1);
uniform_single!(uniform_u128x1_halfm1_single, u128, 0, HALF_128_BIT_UNSIGNED - 1, 1);
uniform_single!(uniform_u128x1_6_single, u128, 0, 6u128, 1);

uniform_inclusive!(uniform_u128x10_all_new_inclusive, u128, 0, u128::max_value(), 10);
uniform_sample!(uniform_u128x10_allm1_new, u128, 0, u128::max_value(), 10);
uniform_sample!(uniform_u128x10_halfp1_new, u128, 0, HALF_128_BIT_UNSIGNED + 1, 10);
uniform_sample!(uniform_u128x10_half_new, u128, 0, HALF_128_BIT_UNSIGNED, 10);
uniform_sample!(uniform_u128x10_halfm1_new, u128, 0, HALF_128_BIT_UNSIGNED - 1, 10);
uniform_sample!(uniform_u128x10_6_new, u128, 0, 6u128, 10);

uniform_single!(uniform_u128x10_allm1_single, u128, 0, u128::max_value(), 10);
uniform_single!(uniform_u128x10_halfp1_single, u128, 0, HALF_128_BIT_UNSIGNED + 1, 10);
uniform_single!(uniform_u128x10_half_single, u128, 0, HALF_128_BIT_UNSIGNED, 10);
uniform_single!(uniform_u128x10_halfm1_single, u128, 0, HALF_128_BIT_UNSIGNED - 1, 10);
uniform_single!(uniform_u128x10_6_single, u128, 0, 6u128, 10);
