// Copyright 2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Implement benchmarks for uniform distributions over integer types

use core::time::Duration;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::distr::uniform::{SampleRange, Uniform};
use rand::prelude::*;
use rand_chacha::ChaCha8Rng;
use rand_pcg::{Pcg32, Pcg64};

const WARM_UP_TIME: Duration = Duration::from_millis(1000);
const MEASUREMENT_TIME: Duration = Duration::from_secs(3);
const SAMPLE_SIZE: usize = 100_000;
const N_RESAMPLES: usize = 10_000;

macro_rules! sample {
    ($R:ty, $T:ty, $U:ty, $g:expr) => {
        $g.bench_function(BenchmarkId::new(stringify!($R), "single"), |b| {
            let mut rng = <$R>::from_rng(&mut rand::rng());
            let x = rng.random::<$U>();
            let bits = (<$T>::BITS / 2);
            let mask = (1 as $U).wrapping_neg() >> bits;
            let range = (x >> bits) * (x & mask);
            let low = <$T>::MIN;
            let high = low.wrapping_add(range as $T);

            b.iter(|| (low..=high).sample_single(&mut rng));
        });

        $g.bench_function(BenchmarkId::new(stringify!($R), "distr"), |b| {
            let mut rng = <$R>::from_rng(&mut rand::rng());
            let x = rng.random::<$U>();
            let bits = (<$T>::BITS / 2);
            let mask = (1 as $U).wrapping_neg() >> bits;
            let range = (x >> bits) * (x & mask);
            let low = <$T>::MIN;
            let high = low.wrapping_add(range as $T);
            let dist = Uniform::<$T>::new_inclusive(<$T>::MIN, high).unwrap();

            b.iter(|| dist.sample(&mut rng));
        });
    };

    ($c:expr, $T:ty, $U:ty) => {{
        let mut g = $c.benchmark_group(concat!("sample", stringify!($T)));
        g.sample_size(SAMPLE_SIZE);
        g.warm_up_time(WARM_UP_TIME);
        g.measurement_time(MEASUREMENT_TIME);
        g.nresamples(N_RESAMPLES);
        sample!(SmallRng, $T, $U, g);
        sample!(ChaCha8Rng, $T, $U, g);
        sample!(Pcg32, $T, $U, g);
        sample!(Pcg64, $T, $U, g);
        g.finish();
    }};
}

fn sample(c: &mut Criterion) {
    sample!(c, i8, u8);
    sample!(c, i16, u16);
    sample!(c, i32, u32);
    sample!(c, i64, u64);
    sample!(c, i128, u128);
}

criterion_group! {
    name = benches;
    config = Criterion::default();
    targets = sample
}
criterion_main!(benches);
