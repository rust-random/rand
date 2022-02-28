// Copyright 2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use criterion::{criterion_group, criterion_main};
use criterion::{BenchmarkId, Criterion};
use rand::distributions::uniform::{SampleUniform, Uniform, UniformSampler};
use rand::prelude::*;

// TODO: multiple RNGs
type BenchRng = SmallRng;

macro_rules! bench_distr_int_group {
    ($name:literal, $T:ty, $f:ident, $g:expr, $inputs:expr) => {
        for input in $inputs {
            $g.bench_with_input(
                BenchmarkId::new($name, input.0),
                &input.1,
                |b, (low, high)| {
                    let mut rng = BenchRng::from_entropy();
                    let dist = Uniform::new_inclusive(low, high);
                    b.iter(|| <$T as SampleUniform>::Sampler::$f(&dist.0, &mut rng))
                },
            );
        }
    };
}

macro_rules! bench_single_int_group {
    ($name:literal, $T:ty, $f:ident, $g:expr, $inputs:expr) => {
        for input in $inputs {
            $g.bench_with_input(
                BenchmarkId::new($name, input.0),
                &input.1,
                |b, (low, high)| {
                    let mut rng = BenchRng::from_entropy();
                    b.iter(|| <$T as SampleUniform>::Sampler::$f(low, high, &mut rng))
                },
            );
        }
        $g.bench_function(BenchmarkId::new($name, "varying"), |b| {
            let (low, mut high) = ($inputs[0].1 .0, $inputs[1].1 .1);
            let mut rng = BenchRng::from_entropy();
            b.iter(|| {
                high = high.wrapping_add(1);
                <$T as SampleUniform>::Sampler::$f(low, high, &mut rng)
            })
        });
    };
}

/// Implement benchmarks for integer types
///
/// This benchmark consists of two groups:
///
/// -   `uniform_distr_int_*`: construct a distribution then sample from it repeatedly
/// -   `uniform_single_int_*`: use sample_single_inclusive methods, using a different range each time
///
/// For each group, we have the following methods:
///
/// -   Old: prior implementation of this method as a baseline
/// -   Lemire: widening multiply with rejection test
/// -   Canon: widening multiply using max(64, ty-bits) sample with bias reduction adjustment
/// -   Canon32 (TODO): Canon's method with 32-bit samples (up to two bias reduction steps)
/// -   Canon64: for 8- and 16-bit types this is just biased widening multiply; for 128-bit
///     types this is Canon's method with 64-bit sample
/// -   Canon-Lemire: as Canon but with more precise bias-reduction step trigger
/// -   Bitmask: bitmasking + rejection method
macro_rules! bench_int {
    ($c:expr, $T:ty, $high:expr) => {{
        let inputs = &[("high_reject", $high), ("low_reject", (-1, 2))];

        let mut g = $c.benchmark_group(concat!("uniform_distr_int_", stringify!($T)));
        bench_distr_int_group!("Old", $T, sample, g, inputs);
        bench_distr_int_group!("Lemire", $T, sample_lemire, g, inputs);
        bench_distr_int_group!("Canon", $T, sample_canon, g, inputs);
        bench_distr_int_group!("Canon64", $T, sample_canon_64, g, inputs);
        bench_distr_int_group!("Canon-Lemire", $T, sample_canon_lemire, g, inputs);
        bench_distr_int_group!("Bitmask", $T, sample_bitmask, g, inputs);
        drop(g);

        let mut g = $c.benchmark_group(concat!("uniform_single_int_", stringify!($T)));
        bench_single_int_group!("Old", $T, sample_single_inclusive, g, inputs);
        bench_single_int_group!("ONeill", $T, sample_single_inclusive_oneill, g, inputs);
        bench_single_int_group!("Canon", $T, sample_single_inclusive_canon, g, inputs);
        bench_single_int_group!("Canon64", $T, sample_single_inclusive_canon_64, g, inputs);
        bench_single_int_group!("Canon-Lemire", $T, sample_inclusive_canon_lemire, g, inputs);
        bench_single_int_group!("Bitmask", $T, sample_single_inclusive_bitmask, g, inputs);
    }};
}

fn uniform_int(c: &mut Criterion) {
    // for i8/i16, we use 32-bit integers internally so rejection is most common near full-size
    // the exact values were determined with an exhaustive search
    bench_int!(c, i8, (i8::MIN, 116));
    bench_int!(c, i16, (i16::MIN, 32407));
    bench_int!(c, i32, (i32::MIN, 1));
    bench_int!(c, i64, (i64::MIN, 1));
    bench_int!(c, i128, (i128::MIN, 1));
}

criterion_group! {
    name = benches;
    config = Criterion::default();
    targets = uniform_int
}
criterion_main!(benches);
