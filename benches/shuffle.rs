// Copyright 2018-2023 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rand::prelude::*;
use rand::SeedableRng;

criterion_group!(
name = benches;
config = Criterion::default();
targets = bench
);
criterion_main!(benches);

pub fn bench(c: &mut Criterion) {
    bench_rng::<rand_chacha::ChaCha12Rng>(c, "ChaCha12");
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
            c.bench_function(
                format!("partial_shuffle_{length}_{rng_name}").as_str(),
                |b| {
                    let mut rng = Rng::seed_from_u64(123);
                    let mut vec: Vec<usize> = (0..length).collect();
                    b.iter(|| {
                        vec.partial_shuffle(&mut rng, length / 2);
                        vec[0]
                    })
                },
            );
        }
    }
}
