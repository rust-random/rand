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
use std::mem::size_of;
use std::num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8};
use std::time::Duration;
use test::Bencher;

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
distr!(distr_standard_alphanumeric, char, Alphanumeric);
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
                    accum = accum.wrapping_add(rng.gen_range($low, high));
                    // force recalculation of range each time
                    high = high.wrapping_add(1) & std::$ty::MAX;
                }
                accum
            });
            b.bytes = size_of::<$ty>() as u64 * RAND_BENCH_N;
        }
    };
}

gen_range_int!(gen_range_i8, i8, -20i8, 100);
gen_range_int!(gen_range_i16, i16, -500i16, 2000);
gen_range_int!(gen_range_i32, i32, -200_000_000i32, 800_000_000);
gen_range_int!(gen_range_i64, i64, 3i64, 123_456_789_123);
gen_range_int!(gen_range_i128, i128, -12345678901234i128, 123_456_789_123_456_789);

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
                    accum += rng.gen_range(low, high);
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
