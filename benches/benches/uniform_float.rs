// Copyright 2023 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Implement benchmarks for uniform distributions over FP types
//!
//! Sampling methods compared:
//!
//! -   sample: current method: (x12 - 1.0) * (b - a) + a

use chacha20::ChaCha8Rng;
use core::time::Duration;
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use rand::distr::uniform::{SampleUniform, Uniform, UniformSampler};
use rand::prelude::*;
use rand_pcg::{Pcg32, Pcg64};

const WARM_UP_TIME: Duration = Duration::from_millis(1000);
const MEASUREMENT_TIME: Duration = Duration::from_secs(3);
const SAMPLE_SIZE: usize = 100_000;
const N_RESAMPLES: usize = 10_000;

macro_rules! single_random {
    ($R:ty, $T:ty, $g:expr) => {
        $g.bench_function(BenchmarkId::new(stringify!($T), stringify!($R)), |b| {
            let mut rng = <$R>::from_rng(&mut rand::rng());
            let (mut low, mut high);
            loop {
                low = <$T>::from_bits(rng.random());
                high = <$T>::from_bits(rng.random());
                if (low < high) && (high - low).is_normal() {
                    break;
                }
            }

            b.iter(|| <$T as SampleUniform>::Sampler::sample_single_inclusive(low, high, &mut rng));
        });
    };

    ($c:expr, $T:ty) => {{
        let mut g = $c.benchmark_group("uniform_single");
        g.sample_size(SAMPLE_SIZE);
        g.warm_up_time(WARM_UP_TIME);
        g.measurement_time(MEASUREMENT_TIME);
        g.nresamples(N_RESAMPLES);
        single_random!(SmallRng, $T, g);
        single_random!(ChaCha8Rng, $T, g);
        single_random!(Pcg32, $T, g);
        single_random!(Pcg64, $T, g);
        g.finish();
    }};
}

fn single_random(c: &mut Criterion) {
    single_random!(c, f32);
    single_random!(c, f64);
}

macro_rules! distr_random {
    ($R:ty, $T:ty, $g:expr) => {
        $g.bench_function(BenchmarkId::new(stringify!($T), stringify!($R)), |b| {
            let mut rng = <$R>::from_rng(&mut rand::rng());
            let dist = loop {
                let low = <$T>::from_bits(rng.random());
                let high = <$T>::from_bits(rng.random());
                if let Ok(dist) = Uniform::<$T>::new_inclusive(low, high) {
                    break dist;
                }
            };

            b.iter(|| dist.sample(&mut rng));
        });
    };

    ($c:expr, $T:ty) => {{
        let mut g = $c.benchmark_group("uniform_distribution");
        g.sample_size(SAMPLE_SIZE);
        g.warm_up_time(WARM_UP_TIME);
        g.measurement_time(MEASUREMENT_TIME);
        g.nresamples(N_RESAMPLES);
        distr_random!(SmallRng, $T, g);
        distr_random!(ChaCha8Rng, $T, g);
        distr_random!(Pcg32, $T, g);
        distr_random!(Pcg64, $T, g);
        g.finish();
    }};
}

fn distr_random(c: &mut Criterion) {
    distr_random!(c, f32);
    distr_random!(c, f64);
}

criterion_group! {
    name = benches;
    config = Criterion::default();
    targets = single_random, distr_random
}
criterion_main!(benches);
