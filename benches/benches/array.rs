// Copyright 2018-2023 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Generating/filling arrays and iterators of output

use criterion::{criterion_group, criterion_main, Criterion};
use rand::distr::Standard;
use rand::prelude::*;
use rand_pcg::Pcg64Mcg;

criterion_group!(
    name = benches;
    config = Criterion::default();
    targets = bench
);
criterion_main!(benches);

pub fn bench(c: &mut Criterion) {
    let mut g = c.benchmark_group("random_1kb");
    g.throughput(criterion::Throughput::Bytes(1024));

    g.bench_function("u16_iter_repeat", |b| {
        use core::iter;
        let mut rng = Pcg64Mcg::from_rng(&mut rand::rng());
        b.iter(|| {
            let v: Vec<u16> = iter::repeat(()).map(|()| rng.random()).take(512).collect();
            v
        });
    });

    g.bench_function("u16_sample_iter", |b| {
        let mut rng = Pcg64Mcg::from_rng(&mut rand::rng());
        b.iter(|| {
            let v: Vec<u16> = Standard.sample_iter(&mut rng).take(512).collect();
            v
        });
    });

    g.bench_function("u16_gen_array", |b| {
        let mut rng = Pcg64Mcg::from_rng(&mut rand::rng());
        b.iter(|| {
            let v: [u16; 512] = rng.random();
            v
        });
    });

    g.bench_function("u16_fill", |b| {
        let mut rng = Pcg64Mcg::from_rng(&mut rand::rng());
        let mut buf = [0u16; 512];
        b.iter(|| {
            rng.fill(&mut buf[..]);
            buf
        });
    });

    g.bench_function("u64_iter_repeat", |b| {
        use core::iter;
        let mut rng = Pcg64Mcg::from_rng(&mut rand::rng());
        b.iter(|| {
            let v: Vec<u64> = iter::repeat(()).map(|()| rng.random()).take(128).collect();
            v
        });
    });

    g.bench_function("u64_sample_iter", |b| {
        let mut rng = Pcg64Mcg::from_rng(&mut rand::rng());
        b.iter(|| {
            let v: Vec<u64> = Standard.sample_iter(&mut rng).take(128).collect();
            v
        });
    });

    g.bench_function("u64_gen_array", |b| {
        let mut rng = Pcg64Mcg::from_rng(&mut rand::rng());
        b.iter(|| {
            let v: [u64; 128] = rng.random();
            v
        });
    });

    g.bench_function("u64_fill", |b| {
        let mut rng = Pcg64Mcg::from_rng(&mut rand::rng());
        let mut buf = [0u64; 128];
        b.iter(|| {
            rng.fill(&mut buf[..]);
            buf
        });
    });
}
