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
    c.bench_function("seq_slice_choose_1_of_100", |b| {
        let mut rng = Pcg32::from_rng(&mut rand::rng());
        let mut buf = [0i32; 100];
        rng.fill(&mut buf);
        let x = black_box(&mut buf);

        b.iter(|| x.choose(&mut rng).unwrap());
    });

    let lens = [(1, 1000), (950, 1000), (10, 100), (90, 100)];
    for (amount, len) in lens {
        let name = format!("seq_slice_sample_{amount}_of_{len}");
        c.bench_function(name.as_str(), |b| {
            let mut rng = Pcg32::from_rng(&mut rand::rng());
            let mut buf = [0i32; 1000];
            rng.fill(&mut buf);
            let x = black_box(&buf[..len]);

            let mut results_buf = [0i32; 950];
            let y = black_box(&mut results_buf[..amount]);
            let amount = black_box(amount);

            b.iter(|| {
                // Collect full result to prevent unwanted shortcuts getting
                // first element (in case sample_indices returns an iterator).
                for (slot, sample) in y.iter_mut().zip(x.sample(&mut rng, amount)) {
                    *slot = *sample;
                }
                y[amount - 1]
            })
        });
    }

    let lens = [(1, 1000), (950, 1000), (10, 100), (90, 100)];
    for (amount, len) in lens {
        let name = format!("seq_slice_sample_weighted_{amount}_of_{len}");
        c.bench_function(name.as_str(), |b| {
            let mut rng = Pcg32::from_rng(&mut rand::rng());
            let mut buf = [0i32; 1000];
            rng.fill(&mut buf);
            let x = black_box(&buf[..len]);

            let mut results_buf = [0i32; 950];
            let y = black_box(&mut results_buf[..amount]);
            let amount = black_box(amount);

            b.iter(|| {
                // Collect full result to prevent unwanted shortcuts getting
                // first element (in case sample_indices returns an iterator).
                let samples_iter = x.sample_weighted(&mut rng, amount, |_| 1.0).unwrap();
                for (slot, sample) in y.iter_mut().zip(samples_iter) {
                    *slot = *sample;
                }
                y[amount - 1]
            })
        });
    }

    c.bench_function("seq_iter_sample_10_of_100", |b| {
        let mut rng = Pcg32::from_rng(&mut rand::rng());
        let mut buf = [0i32; 100];
        rng.fill(&mut buf);
        let x = black_box(&buf);
        b.iter(|| x.iter().cloned().sample(&mut rng, 10))
    });

    c.bench_function("seq_iter_sample_fill_10_of_100", |b| {
        let mut rng = Pcg32::from_rng(&mut rand::rng());
        let mut buf = [0i32; 100];
        rng.fill(&mut buf);
        let x = black_box(&buf);
        let mut buf = [0; 10];
        b.iter(|| x.iter().cloned().sample_fill(&mut rng, &mut buf))
    });

    bench_rng::<chacha20::ChaCha20Rng>(c, "ChaCha20");
    bench_rng::<rand_pcg::Pcg32>(c, "Pcg32");
    bench_rng::<rand_pcg::Pcg64>(c, "Pcg64");
}

fn bench_rng<Rng: RngCore + SeedableRng>(c: &mut Criterion, rng_name: &'static str) {
    for length in [1, 2, 3, 10, 100, 1000].map(black_box) {
        let name = format!("choose_size-hinted_from_{length}_{rng_name}");
        c.bench_function(name.as_str(), |b| {
            let mut rng = Rng::seed_from_u64(123);
            b.iter(|| choose_size_hinted(length, &mut rng))
        });

        let name = format!("choose_stable_from_{length}_{rng_name}");
        c.bench_function(name.as_str(), |b| {
            let mut rng = Rng::seed_from_u64(123);
            b.iter(|| choose_stable(length, &mut rng))
        });

        let name = format!("choose_unhinted_from_{length}_{rng_name}");
        c.bench_function(name.as_str(), |b| {
            let mut rng = Rng::seed_from_u64(123);
            b.iter(|| choose_unhinted(length, &mut rng))
        });

        let name = format!("choose_windowed_from_{length}_{rng_name}");
        c.bench_function(name.as_str(), |b| {
            let mut rng = Rng::seed_from_u64(123);
            b.iter(|| choose_windowed(length, 7, &mut rng))
        });
    }
}

fn choose_size_hinted<R: Rng>(max: usize, rng: &mut R) -> Option<usize> {
    let iterator = 0..max;
    iterator.choose(rng)
}

fn choose_stable<R: Rng>(max: usize, rng: &mut R) -> Option<usize> {
    let iterator = 0..max;
    iterator.choose_stable(rng)
}

fn choose_unhinted<R: Rng>(max: usize, rng: &mut R) -> Option<usize> {
    let iterator = UnhintedIterator { iter: (0..max) };
    iterator.choose(rng)
}

fn choose_windowed<R: Rng>(max: usize, window_size: usize, rng: &mut R) -> Option<usize> {
    let iterator = WindowHintedIterator {
        iter: (0..max),
        window_size,
    };
    iterator.choose(rng)
}

#[derive(Clone)]
struct UnhintedIterator<I: Iterator + Clone> {
    iter: I,
}
impl<I: Iterator + Clone> Iterator for UnhintedIterator<I> {
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

#[derive(Clone)]
struct WindowHintedIterator<I: ExactSizeIterator + Iterator + Clone> {
    iter: I,
    window_size: usize,
}
impl<I: ExactSizeIterator + Iterator + Clone> Iterator for WindowHintedIterator<I> {
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (core::cmp::min(self.iter.len(), self.window_size), None)
    }
}
