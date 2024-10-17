// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Generating/filling arrays and iterators of output

use criterion::{criterion_group, criterion_main, Criterion};
use rand::distr::Bernoulli;
use rand::prelude::*;
use rand_pcg::Pcg32;

criterion_group!(
    name = benches;
    config = Criterion::default();
    targets = bench
);
criterion_main!(benches);

pub fn bench(c: &mut Criterion) {
    let mut g = c.benchmark_group("random_bool");
    g.sample_size(1000);
    g.warm_up_time(core::time::Duration::from_millis(500));
    g.measurement_time(core::time::Duration::from_millis(1000));

    g.bench_function("standard", |b| {
        let mut rng = Pcg32::from_rng(&mut rand::rng());
        b.iter(|| rng.sample::<bool, _>(rand::distr::Standard))
    });

    g.bench_function("const", |b| {
        let mut rng = Pcg32::from_rng(&mut rand::rng());
        b.iter(|| rng.random_bool(0.18))
    });

    g.bench_function("var", |b| {
        let mut rng = Pcg32::from_rng(&mut rand::rng());
        let p = rng.random();
        b.iter(|| rng.random_bool(p))
    });

    g.bench_function("ratio_const", |b| {
        let mut rng = Pcg32::from_rng(&mut rand::rng());
        b.iter(|| rng.random_ratio(2, 3))
    });

    g.bench_function("ratio_var", |b| {
        let mut rng = Pcg32::from_rng(&mut rand::rng());
        let d = rng.random_range(1..=100);
        let n = rng.random_range(0..=d);
        b.iter(|| rng.random_ratio(n, d));
    });

    g.bench_function("bernoulli_const", |b| {
        let mut rng = Pcg32::from_rng(&mut rand::rng());
        let d = Bernoulli::new(0.18).unwrap();
        b.iter(|| rng.sample(d))
    });

    g.bench_function("bernoulli_var", |b| {
        let mut rng = Pcg32::from_rng(&mut rand::rng());
        let p = rng.random();
        let d = Bernoulli::new(p).unwrap();
        b.iter(|| rng.sample(d))
    });
}
