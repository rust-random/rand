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
//! -   Canon32 (TODO): Canon's method with 32-bit samples (up to two bias reduction steps)
//! -   Canon64: for 8- and 16-bit types this is just biased widening multiply; for 128-bit
//!     types this is Canon's method with 64-bit sample
//! -   Canon-Lemire: as Canon but with more precise bias-reduction step trigger
//! -   Bitmask: bitmasking + rejection method

use criterion::{criterion_group, criterion_main};
use criterion::{BenchmarkId, Criterion};
use rand::distributions::uniform::{SampleUniform, Uniform, UniformSampler};
use rand::prelude::*;

// TODO: multiple RNGs
type BenchRng = SmallRng;

macro_rules! single_random {
    ($name:literal, $T:ty, $f:ident, $g:expr) => {
        $g.bench_function(BenchmarkId::new($name, "SmallRng"), |b| {
            let low = <$T>::MIN;
            let mut rng = BenchRng::from_entropy();
            b.iter(|| {
                let high: $T = rng.gen();
                <$T as SampleUniform>::Sampler::$f(low, high, &mut rng)
            })
        });
    };

    ($c:expr, $T:ty) => {{
        let mut g = $c.benchmark_group(concat!("single_random_", stringify!($T)));
        single_random!("Old", $T, sample_single_inclusive, g);
        single_random!("ONeill", $T, sample_single_inclusive_oneill, g);
        single_random!("Canon-Unbiased", $T, sample_single_inclusive_canon_unbiased, g);
        single_random!("Canon", $T, sample_single_inclusive_canon, g);
        single_random!("Canon64", $T, sample_single_inclusive_canon_64, g);
        single_random!("Canon-Lemire", $T, sample_inclusive_canon_lemire, g);
        single_random!("Bitmask", $T, sample_single_inclusive_bitmask, g);
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
    ($name:literal, $T:ty, $f:ident, $g:expr, $range:expr) => {
        $g.bench_function(BenchmarkId::new($name, "SmallRng"), |b| {
            let mut rng = BenchRng::from_entropy();
            let dist = Uniform::<$T>::new_inclusive($range.0, $range.1);
            b.iter(|| <$T as SampleUniform>::Sampler::$f(&dist.0, &mut rng))
        });
    };
}

macro_rules! distr_low_reject {
    ($c:expr, $T:ty) => {{
        let mut g = $c.benchmark_group(concat!("distr_low_reject_", stringify!($T)));
        distr_range!("Old", $T, sample, g, (-1, 2));
        distr_range!("Lemire", $T, sample_lemire, g, (-1, 2));
        distr_range!("Canon-Unbiased", $T, sample_canon_unbiased, g, (-1, 2));
        distr_range!("Canon", $T, sample_canon, g, (-1, 2));
        distr_range!("Canon64", $T, sample_canon_64, g, (-1, 2));
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
        distr_range!("Old", $T, sample, g, $range);
        distr_range!("Lemire", $T, sample_lemire, g, $range);
        distr_range!("Canon-Unbiased", $T, sample_canon_unbiased, g, $range);
        distr_range!("Canon", $T, sample_canon, g, $range);
        distr_range!("Canon64", $T, sample_canon_64, g, $range);
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

criterion_group! {
    name = benches;
    config = Criterion::default();
    targets = single_random, distr_low_reject, distr_high_reject
}
criterion_main!(benches);
