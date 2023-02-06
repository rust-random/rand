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
//! -   Canon32: Canon's method with max(32,size)-bit samples (at most one bias reduction step)
//! -   Canon-reduced: for 8-32 bit types this is a single max(64, size) bit
//!     sample (biased) using widening multiply; for larger sizes this is Canon
//!     but using half the bit-width for the bias reduction sample.
//! -   Canon32-2: max(32, size) bit sample, optionally followed by one or two 32-bit bias reduction steps
//! -   Canon-Lemire: as Canon but with more precise bias-reduction step trigger

use core::time::Duration;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::distributions::uniform::{SampleUniform, Uniform, UniformSampler};
use rand::prelude::*;
use rand_chacha::ChaCha8Rng;
use rand_pcg::{Pcg32, Pcg64};

const WARM_UP_TIME: Duration = Duration::from_millis(100);
const MEASUREMENT_TIME: Duration = Duration::from_secs(1);

macro_rules! single_random {
    ($name:literal, $R:ty, $T:ty, $U:ty, $f:ident, $g:expr) => {
        $g.bench_function(BenchmarkId::new(stringify!($R), $name), |b| {
            let mut rng = <$R>::from_entropy();
            let x = rng.gen::<$U>();
            let bits = (<$T>::BITS / 2);
            let mask = (1 as $U).wrapping_neg() >> bits;
            let range = (x >> bits) * (x & mask);
            let low = <$T>::MIN;
            let high = low.wrapping_add(range as $T);
            const SAMPLES: usize = 50;
            b.iter(|| {
                let mut result: $T = 0;
                for _ in 0..SAMPLES {
                    result =
                        result.wrapping_add(<$T as SampleUniform>::Sampler::$f(low, high, &mut rng));
                }
                result
            });
        });
    };

    ($R:ty, $T:ty, $U:ty, $g:expr) => {
        single_random!("Old", $R, $T, $U, sample_single_inclusive, $g);
        single_random!("ONeill", $R, $T, $U, sample_single_inclusive_oneill, $g);
        single_random!("Canon-Unbiased", $R, $T, $U, sample_single_inclusive_canon_unbiased, $g);
        single_random!("Canon", $R, $T, $U, sample_single_inclusive_canon, $g);
        single_random!("Canon32", $R, $T, $U, sample_single_inclusive_canon_u32, $g);
        single_random!("Canon-reduced", $R, $T, $U, sample_single_inclusive_canon_reduced, $g);
        single_random!("Canon32-2", $R, $T, $U, sample_single_inclusive_canon_u32_2, $g);
        single_random!("Canon-Lemire", $R, $T, $U, sample_inclusive_canon_lemire, $g);
    };

    ($c:expr, $T:ty, $U:ty) => {{
        let mut g = $c.benchmark_group(concat!("single_random_", stringify!($T)));
        g.warm_up_time(WARM_UP_TIME);
        g.measurement_time(MEASUREMENT_TIME);
        single_random!(SmallRng, $T, $U, g);
        single_random!(ChaCha8Rng, $T, $U, g);
        single_random!(Pcg32, $T, $U, g);
        single_random!(Pcg64, $T, $U, g);
        g.finish();
    }};
}

fn single_random(c: &mut Criterion) {
    single_random!(c, i8, u8);
    single_random!(c, i16, u16);
    single_random!(c, i32, u32);
    single_random!(c, i64, u64);
    single_random!(c, i128, u128);
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
        distr_random!("Canon32-2", $T, $U, sample_canon_u32_2, g);
        distr_random!("Canon-Lemire", $T, $U, sample_canon_lemire, g);
        g.finish();
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
    targets = single_random, distr_random
}
criterion_main!(benches);
