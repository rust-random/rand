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

use rand::distr::{Alphanumeric, Open01, OpenClosed01, Standard};
use core::mem::size_of;
use core::num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8};
use test::Bencher;

use rand::prelude::*;

// At this time, distributions are optimised for 64-bit platforms.
use rand_pcg::Pcg64Mcg;

macro_rules! distr_int {
    ($fnn:ident, $ty:ty, $distr:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = Pcg64Mcg::from_os_rng();
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
            let mut rng = Pcg64Mcg::from_os_rng();
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
            let mut rng = Pcg64Mcg::from_os_rng();
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

macro_rules! distr {
    ($fnn:ident, $ty:ty, $distr:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = Pcg64Mcg::from_os_rng();
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

distr!(distr_standard_alphanumeric, u8, Alphanumeric);
distr!(distr_standard_codepoint, char, Standard);

distr_float!(distr_standard_f32, f32, Standard);
distr_float!(distr_standard_f64, f64, Standard);
distr_float!(distr_open01_f32, f32, Open01);
distr_float!(distr_open01_f64, f64, Open01);
distr_float!(distr_openclosed01_f32, f32, OpenClosed01);
distr_float!(distr_openclosed01_f64, f64, OpenClosed01);
