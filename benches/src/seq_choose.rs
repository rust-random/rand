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
    bench_rng::<rand_chacha::ChaCha20Rng>(c, "ChaCha20");
    bench_rng::<rand_pcg::Pcg32>(c, "Pcg32");
    bench_rng::<rand_pcg::Pcg64>(c, "Pcg64");
}

fn bench_rng<Rng: RngCore + SeedableRng>(c: &mut Criterion, rng_name: &'static str) {
    for length in [1, 2, 3, 10, 100, 1000].map(black_box) {
        c.bench_function(
            format!("choose_size-hinted_from_{length}_{rng_name}").as_str(),
            |b| {
                let mut rng = Rng::seed_from_u64(123);
                b.iter(|| choose_size_hinted(length, &mut rng))
            },
        );

        c.bench_function(
            format!("choose_stable_from_{length}_{rng_name}").as_str(),
            |b| {
                let mut rng = Rng::seed_from_u64(123);
                b.iter(|| choose_stable(length, &mut rng))
            },
        );

        c.bench_function(
            format!("choose_unhinted_from_{length}_{rng_name}").as_str(),
            |b| {
                let mut rng = Rng::seed_from_u64(123);
                b.iter(|| choose_unhinted(length, &mut rng))
            },
        );

        c.bench_function(
            format!("choose_windowed_from_{length}_{rng_name}").as_str(),
            |b| {
                let mut rng = Rng::seed_from_u64(123);
                b.iter(|| choose_windowed(length, 7, &mut rng))
            },
        );
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
