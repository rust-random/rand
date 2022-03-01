// Copyright 2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Implement benchmarks for uniform distributions over integer types
//!
//! Sampling methods compared:
//!
//! -   Old: prior implementation of this method as a baseline
//! -   Lemire: widening multiply with rejection test
//! -   Canon: widening multiply using max(64, ty-bits) sample with bias reduction adjustment
//! -   Canon32: Canon's method with 32-bit samples (at most one bias reduction step)
//! -   Canon-reduced: for 8-, 16- and 32-bit types this is just biased widening multiply; for
//!     64- and 128-bit types this is Canon's method with half-size sample (single step)
//! -   Canon-Lemire: as Canon but with more precise bias-reduction step trigger
//! -   Bitmask: bitmasking + rejection method

use core::time::Duration;
use criterion::{criterion_group, criterion_main};
use criterion::{BenchmarkId, Criterion};
use rand::distributions::uniform::{SampleUniform, Uniform, UniformSampler};
use rand::prelude::*;
use rand_chacha::ChaCha8Rng;
use rand_pcg::{Pcg32, Pcg64};

const WARM_UP_TIME: Duration = Duration::from_millis(100);
const MEASUREMENT_TIME: Duration = Duration::from_secs(1);

macro_rules! single_random {
    ($name:literal, $R:ty, $T:ty, $f:ident, $g:expr) => {
        $g.bench_function(BenchmarkId::new(stringify!($R), $name), |b| {
            let low = <$T>::MIN;
            let mut rng = <$R>::from_entropy();
            b.iter(|| {
                let high: $T = rng.gen();
                <$T as SampleUniform>::Sampler::$f(low, high, &mut rng)
            })
        });
    };

    ($R:ty, $T:ty, $g:expr) => {
        single_random!("Old", $R, $T, sample_single_inclusive, $g);
        single_random!("ONeill", $R, $T, sample_single_inclusive_oneill, $g);
        single_random!("Canon-Unbiased", $R, $T, sample_single_inclusive_canon_unbiased, $g);
        single_random!("Canon", $R, $T, sample_single_inclusive_canon, $g);
        single_random!("Canon32", $R, $T, sample_single_inclusive_canon_u32, $g);
        single_random!("Canon-reduced", $R, $T, sample_single_inclusive_canon_reduced, $g);
        single_random!("Canon-Lemire", $R, $T, sample_inclusive_canon_lemire, $g);
        single_random!("Bitmask", $R, $T, sample_single_inclusive_bitmask, $g);
    };

    ($c:expr, $T:ty) => {{
        let mut g = $c.benchmark_group(concat!("single_random_", stringify!($T)));
        g.warm_up_time(WARM_UP_TIME);
        g.measurement_time(MEASUREMENT_TIME);
        single_random!(SmallRng, $T, g);
        single_random!(ChaCha8Rng, $T, g);
        single_random!(Pcg32, $T, g);
        single_random!(Pcg64, $T, g);
    }};
}

fn single_random(c: &mut Criterion) {
    single_random!(c, i8);
    single_random!(c, i16);
    single_random!(c, i32);
    single_random!(c, i64);
    single_random!(c, i128);
}

macro_rules! distr_range {
    ($name:literal, $R:ty, $T:ty, $f:ident, $g:expr, $range:expr) => {
        $g.bench_function(BenchmarkId::new(stringify!($R), $name), |b| {
            let mut rng = <$R>::from_entropy();
            let dist = Uniform::<$T>::new_inclusive($range.0, $range.1);
            b.iter(|| <$T as SampleUniform>::Sampler::$f(&dist.0, &mut rng))
        });
    };

    ($name:literal, $T:ty, $f:ident, $g:expr, $range:expr) => {
        distr_range!($name, SmallRng, $T, $f, $g, $range);
        distr_range!($name, ChaCha8Rng, $T, $f, $g, $range);
        distr_range!($name, Pcg32, $T, $f, $g, $range);
        distr_range!($name, Pcg64, $T, $f, $g, $range);
    };
}

macro_rules! distr_low_reject {
    ($c:expr, $T:ty) => {{
        let mut g = $c.benchmark_group(concat!("distr_low_reject_", stringify!($T)));
        g.warm_up_time(WARM_UP_TIME);
        g.measurement_time(MEASUREMENT_TIME);
        distr_range!("Old", $T, sample, g, (-1, 2));
        distr_range!("Lemire", $T, sample_lemire, g, (-1, 2));
        distr_range!("Canon-Unbiased", $T, sample_canon_unbiased, g, (-1, 2));
        distr_range!("Canon", $T, sample_canon, g, (-1, 2));
        distr_range!("Canon32", $T, sample_canon_u32, g, (-1, 2));
        distr_range!("Canon-reduced", $T, sample_canon_reduced, g, (-1, 2));
        distr_range!("Canon-Lemire", $T, sample_canon_lemire, g, (-1, 2));
        distr_range!("Bitmask", $T, sample_bitmask, g, (-1, 2));
    }};
}

fn distr_low_reject(c: &mut Criterion) {
    distr_low_reject!(c, i8);
    distr_low_reject!(c, i16);
    distr_low_reject!(c, i32);
    distr_low_reject!(c, i64);
    distr_low_reject!(c, i128);
}

macro_rules! distr_high_reject {
    ($c:expr, $T:ty, $range:expr) => {{
        let mut g = $c.benchmark_group(concat!("distr_high_reject_", stringify!($T)));
        g.warm_up_time(WARM_UP_TIME);
        g.measurement_time(MEASUREMENT_TIME);
        distr_range!("Old", $T, sample, g, $range);
        distr_range!("Lemire", $T, sample_lemire, g, $range);
        distr_range!("Canon-Unbiased", $T, sample_canon_unbiased, g, $range);
        distr_range!("Canon", $T, sample_canon, g, $range);
        distr_range!("Canon-reduced", $T, sample_canon_reduced, g, $range);
        distr_range!("Canon-Lemire", $T, sample_canon_lemire, g, $range);
        distr_range!("Bitmask", $T, sample_bitmask, g, $range);
    }};
}

fn distr_high_reject(c: &mut Criterion) {
    // for i8/i16, we use 32-bit integers internally so rejection is most common near full-size
    // the exact values were determined with an exhaustive search
    distr_high_reject!(c, i8, (i8::MIN, 116));
    distr_high_reject!(c, i16, (i16::MIN, 32407));
    distr_high_reject!(c, i32, (i32::MIN, 1));
    distr_high_reject!(c, i64, (i64::MIN, 1));
    distr_high_reject!(c, i128, (i128::MIN, 1));
}

macro_rules! distr_random {
    ($name:literal, $R:ty, $T:ty, $U:ty, $f:ident, $g:expr) => {
        $g.bench_function(BenchmarkId::new(stringify!($R), $name), |b| {
            let mut rng = <$R>::from_entropy();
            let x = rng.gen::<$U>();
            let bits = (<$T>::BITS / 2);
            let mask = (1 as $U).wrapping_neg() >> bits;
            let range = (x >> bits) * (x & mask);
            let high = <$T>::MIN.wrapping_add(range as $T);
            let dist = Uniform::<$T>::new_inclusive(<$T>::MIN, high);
            const SAMPLES: usize = 50;
            b.iter(|| {
                let mut result: $T = 0;
                for _ in 0..SAMPLES {
                    result =
                        result.wrapping_add(<$T as SampleUniform>::Sampler::$f(&dist.0, &mut rng));
                }
                result
            });
        });
    };

    ($name:literal, $T:ty, $U:ty, $f:ident, $g:expr) => {
        distr_random!($name, SmallRng, $T, $U, $f, $g);
        distr_random!($name, ChaCha8Rng, $T, $U, $f, $g);
        distr_random!($name, Pcg32, $T, $U, $f, $g);
        distr_random!($name, Pcg64, $T, $U, $f, $g);
    };

    ($c:expr, $T:ty, $U:ty) => {{
        let mut g = $c.benchmark_group(concat!("distr_random_", stringify!($T)));
        g.warm_up_time(WARM_UP_TIME);
        g.measurement_time(MEASUREMENT_TIME);
        distr_random!("Old", $T, $U, sample, g);
        distr_random!("Lemire", $T, $U, sample_lemire, g);
        distr_random!("Canon-Unbiased", $T, $U, sample_canon_unbiased, g);
        distr_random!("Canon", $T, $U, sample_canon, g);
        distr_random!("Canon32", $T, $U, sample_canon_u32, g);
        distr_random!("Canon-reduced", $T, $U, sample_canon_reduced, g);
        distr_random!("Canon-Lemire", $T, $U, sample_canon_lemire, g);
        distr_random!("Bitmask", $T, $U, sample_bitmask, g);
    }};
}

fn distr_random(c: &mut Criterion) {
    distr_random!(c, i8, u8);
    distr_random!(c, i16, u16);
    distr_random!(c, i32, u32);
    distr_random!(c, i64, u64);
    distr_random!(c, i128, u128);
}

criterion_group! {
    name = benches;
    config = Criterion::default();
    targets = single_random, distr_low_reject, distr_high_reject, distr_random
}
criterion_main!(benches);
