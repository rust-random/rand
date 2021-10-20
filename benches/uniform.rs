// Copyright 2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use criterion::{criterion_group, criterion_main};
use criterion::{BenchmarkId, Criterion};
use rand::distributions::uniform::{SampleUniform, UniformSampler};
use rand::prelude::*;

type BenchRng = SmallRng;

macro_rules! bench_int_group {
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

macro_rules! bench_int {
    ($c:expr, $T:ty, $high:expr) => {{
        let mut g = $c.benchmark_group(concat!("uniform_int_", stringify!($T)));
        let inputs = &[("high_reject", $high), ("low_reject", (-1, 2))];

        bench_int_group!("Old", $T, sample_single_inclusive, g, inputs);
        bench_int_group!("ONeill", $T, sample_single_inclusive_oneill, g, inputs);
        bench_int_group!("Canon", $T, sample_single_inclusive_canon, g, inputs);
        bench_int_group!("Canon-Lemire", $T, sample_inclusive_canon_lemire, g, inputs);
        bench_int_group!("Bitmask", $T, sample_single_inclusive_bitmask, g, inputs);
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
