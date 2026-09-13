// Copyright 2019 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use rand::distr::uniform::SampleUniform;
use rand::distr::weighted::{Weight, WeightedIndex};
use rand::prelude::*;
use rand::seq::index::sample_weighted;

criterion_group!(
    name = benches;
    config = Criterion::default();
    targets = bench
);
criterion_main!(benches);

pub fn bench(c: &mut Criterion) {
    bench_weight_iteration::<u32>(c, "u32");
    bench_weight_iteration::<f64>(c, "f64");

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
        let name = format!("weighted_sample_indices_{amount}_of_{len_name}");
        c.bench_function(name.as_str(), |b| {
            let length = black_box(length);
            let amount = black_box(amount);
            let mut rng: SmallRng = rand::make_rng();
            b.iter(|| sample_weighted(&mut rng, length, |idx| (1 + (idx % 100)) as u32, amount))
        });
    }
}

fn bench_weight_iteration<X>(c: &mut Criterion, name: &str)
where
    X: SampleUniform + Weight + PartialOrd + From<u32> + core::iter::Sum + for<'a> core::ops::SubAssign<&'a X>,
{
    let mut group = c.benchmark_group(format!("weighted_iter/{name}"));
    for length in [1usize, 4, 16, 64, 256, 1024, 16384] {
        let distr = WeightedIndex::new((0..length).map(|i| X::from((1 + i % 10) as u32))).unwrap();
        group.bench_function(BenchmarkId::new("collect", length), |b| {
            b.iter(|| black_box(&distr).weights().collect::<Vec<_>>())
        });

        // Control cases: neither summing nor reusing capacity needs a size hint.
        if [4, 1024].contains(&length) {
            group
                .bench_function(BenchmarkId::new("sum", length), |b| b.iter(|| black_box(&distr).weights().sum::<X>()));
            let mut buffer = Vec::with_capacity(length);
            group.bench_function(BenchmarkId::new("reuse", length), |b| {
                b.iter(|| {
                    buffer.clear();
                    buffer.extend(black_box(&distr).weights());
                    black_box(buffer.as_slice());
                })
            });
        }

        if length == 1024 {
            for (position, index) in [
                ("first", 0),
                ("middle", length / 2),
                ("last", length - 1),
                ("past_end", length),
                ("max_index", usize::MAX),
            ] {
                group.bench_function(BenchmarkId::new("weight", position), |b| {
                    b.iter(|| black_box(&distr).weight(black_box(index)))
                });
            }
            let mut iter = distr.weights();
            // Consume half the weights before timing (nth also consumes its returned item).
            // A skip adapter would defer that work until collection.
            let _ = iter.nth(length / 2 - 1);
            group.bench_function(BenchmarkId::new("collect_remaining", length / 2), |b| {
                b.iter(|| black_box(iter.clone()).collect::<Vec<_>>())
            });
        }
    }
    let distr = WeightedIndex::new([X::from(1)]).unwrap();
    let mut exhausted = distr.weights();
    let _ = exhausted.next();
    group.bench_function(BenchmarkId::new("collect", 0), |b| {
        b.iter(|| black_box(exhausted.clone()).collect::<Vec<_>>())
    });
    group.finish();
}
