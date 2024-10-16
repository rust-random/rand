// Copyright 2019 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rand::distr::WeightedIndex;
use rand::prelude::*;
use rand::seq::index::sample_weighted;

criterion_group!(
    name = benches;
    config = Criterion::default();
    targets = bench
);
criterion_main!(benches);

pub fn bench(c: &mut Criterion) {
    c.bench_function("weighted_index_creation", |b| {
        let mut rng = rand::rng();
        let weights = black_box([1u32, 2, 4, 0, 5, 1, 7, 1, 2, 3, 4, 5, 6, 7]);
        b.iter(|| {
            let distr = WeightedIndex::new(weights.to_vec()).unwrap();
            rng.sample(distr)
        })
    });

    c.bench_function("weighted_index_modification", |b| {
        let mut rng = rand::rng();
        let weights = black_box([1u32, 2, 3, 0, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7]);
        let mut distr = WeightedIndex::new(weights.to_vec()).unwrap();
        b.iter(|| {
            distr.update_weights(&[(2, &4), (5, &1)]).unwrap();
            rng.sample(&distr)
        })
    });

    let lens = [
        (1, 1000, "1k"),
        (10, 1000, "1k"),
        (100, 1000, "1k"),
        (100, 1_000_000, "1M"),
        (200, 1_000_000, "1M"),
        (400, 1_000_000, "1M"),
        (600, 1_000_000, "1M"),
        (1000, 1_000_000, "1M"),
    ];
    for (amount, length, len_name) in lens {
        let name = format!("weighted_sample_indices_{}_of_{}", amount, len_name);
        c.bench_function(name.as_str(), |b| {
            let length = black_box(length);
            let amount = black_box(amount);
            let mut rng = SmallRng::from_rng(&mut rand::rng());
            b.iter(|| sample_weighted(&mut rng, length, |idx| (1 + (idx % 100)) as u32, amount))
        });
    }
}
