// Copyright 2018-2023 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use rand::SeedableRng;
use rand::prelude::*;
use rand_pcg::Pcg32;

criterion_group!(
    name = benches;
    config = Criterion::default();
    targets = bench
);
criterion_main!(benches);

pub fn bench(c: &mut Criterion) {
    c.bench_function("seq_shuffle_100", |b| {
        let mut rng = Pcg32::from_rng(&mut rand::rng());
        let mut buf = [0i32; 100];
        rng.fill(&mut buf);
        let x = black_box(&mut buf);
        b.iter(|| {
            x.shuffle(&mut rng);
            x[0]
        })
    });

    bench_rng::<chacha20::ChaCha12Rng>(c, "ChaCha12");
    bench_rng::<rand_pcg::Pcg32>(c, "Pcg32");
    bench_rng::<rand_pcg::Pcg64>(c, "Pcg64");
}

fn bench_rng<Rng: RngCore + SeedableRng>(c: &mut Criterion, rng_name: &'static str) {
    for length in [1, 2, 3, 10, 100, 1000, 10000].map(black_box) {
        c.bench_function(format!("shuffle_{length}_{rng_name}").as_str(), |b| {
            let mut rng = Rng::seed_from_u64(123);
            let mut vec: Vec<usize> = (0..length).collect();
            b.iter(|| {
                vec.shuffle(&mut rng);
                vec[0]
            })
        });

        if length >= 10 {
            let name = format!("partial_shuffle_{length}_{rng_name}");
            c.bench_function(name.as_str(), |b| {
                let mut rng = Rng::seed_from_u64(123);
                let mut vec: Vec<usize> = (0..length).collect();
                b.iter(|| {
                    vec.partial_shuffle(&mut rng, length / 2);
                    vec[0]
                })
            });
        }
    }
}
