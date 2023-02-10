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
//! -   ONeill: O'Neill's proposed method: https://www.pcg-random.org/posts/bounded-rands.html
//! -   Canon: widening multiply using max(64, ty-bits) sample, followed by one bias-reduction
//!     step at the same sample size where required
//! -   Canon32: as above, but using max(32, ty-bits) sample sizes
//! -   Canon32-2: as above, but with up to two bias-reduction steps
//! -   Canon-Un[biased]: as Canon, but with an unlimited number of bias-reduction steps
//! -   Canon-Red[uced]: Canon's method with max(64, ty-bits) initial sample size and half with
//!     for the bias reduction step steps
//! -   Canon-Red-Un: as Canon-Red, but with an unlimited number of bias reduction steps

use core::time::Duration;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::distributions::uniform::{SampleUniform, Uniform};
use rand::prelude::*;
use rand_chacha::ChaCha8Rng;
use rand_pcg::{Pcg32, Pcg64};

const WARM_UP_TIME: Duration = Duration::from_millis(1000);
const MEASUREMENT_TIME: Duration = Duration::from_secs(3);
const SAMPLE_SIZE: usize = 100_000;
const N_RESAMPLES: usize = 10_000;

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

            b.iter(|| <$T as SampleUniform>::Sampler::$f(low, high, &mut rng));
        });
    };

    ($R:ty, $T:ty, $U:ty, $g:expr) => {
        single_random!("sample", $R, $T, $U, sample_single_inclusive_canon, $g);
        single_random!("sample-unbiased", $R, $T, $U, sample_single_inclusive_canon_unbiased, $g);
    };

    ($c:expr, $T:ty, $U:ty) => {{
        let mut g = $c.benchmark_group(concat!("single_random_", stringify!($T)));
        g.sample_size(SAMPLE_SIZE);
        g.warm_up_time(WARM_UP_TIME);
        g.measurement_time(MEASUREMENT_TIME);
        g.nresamples(N_RESAMPLES);
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
            let low = <$T>::MIN;
            let high = low.wrapping_add(range as $T);
            let dist = Uniform::<$T>::new_inclusive(<$T>::MIN, high);

            b.iter(|| <$T as SampleUniform>::Sampler::$f(&dist.0, &mut rng));
        });
    };

    ($R:ty, $T:ty, $U:ty, $g:expr) => {
        distr_random!("sample", $R, $T, $U, sample, $g);
    };

    ($c:expr, $T:ty, $U:ty) => {{
        let mut g = $c.benchmark_group(concat!("distr_random_", stringify!($T)));
        g.sample_size(SAMPLE_SIZE);
        g.warm_up_time(WARM_UP_TIME);
        g.measurement_time(MEASUREMENT_TIME);
        g.nresamples(N_RESAMPLES);
        distr_random!(SmallRng, $T, $U, g);
        distr_random!(ChaCha8Rng, $T, $U, g);
        distr_random!(Pcg32, $T, $U, g);
        distr_random!(Pcg64, $T, $U, g);
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
