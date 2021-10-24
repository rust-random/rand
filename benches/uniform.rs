// Copyright 2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use criterion::{criterion_group, criterion_main};
use criterion::{BenchmarkId, Criterion};
#[cfg(feature = "simd_support")] use packed_simd::*;
use rand::distributions::uniform::{SampleUniform, Uniform, UniformSampler};
use rand::prelude::*;

type BenchRng = SmallRng;

macro_rules! bench_dist_int_group {
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
        let inputs = &[("high_reject", $high), ("low_reject", (-1, 2))];

        let mut g = $c.benchmark_group(concat!("uniform_dist_int_", stringify!($T)));
        bench_dist_int_group!("Old", $T, sample, g, inputs);
        bench_dist_int_group!("Lemire", $T, sample_lemire, g, inputs);
        bench_dist_int_group!("Canon", $T, sample_canon, g, inputs);
        bench_dist_int_group!("Canon64", $T, sample_canon_64, g, inputs);
        bench_dist_int_group!("Canon-Lemire", $T, sample_canon_lemire, g, inputs);
        bench_dist_int_group!("Bitmask", $T, sample_bitmask, g, inputs);
        drop(g);

        let mut g = $c.benchmark_group(concat!("uniform_int_", stringify!($T)));
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

#[cfg(feature = "simd_support")]
macro_rules! bench_simd_group {
    ($name:literal, $T:ty, $f:ident, $g:expr, $inputs:expr) => {
        for input in $inputs {
            $g.bench_with_input(
                BenchmarkId::new($name, input.0),
                &input.1,
                |b, (low, high)| {
                    let mut rng = BenchRng::from_entropy();
                    let (low, high) = (<$T>::splat(*low), <$T>::splat(*high));
                    b.iter(|| <$T as SampleUniform>::Sampler::$f(low, high, &mut rng))
                },
            );
        }
        $g.bench_function(BenchmarkId::new($name, "varying"), |b| {
            let (low, mut high) = (<$T>::splat($inputs[0].1 .0), <$T>::splat($inputs[1].1 .1));
            let mut rng = BenchRng::from_entropy();
            b.iter(|| {
                high += 1;
                <$T as SampleUniform>::Sampler::$f(low, high, &mut rng)
            })
        });
    };
}

#[cfg(feature = "simd_support")]
macro_rules! bench_simd {
    ($c:expr, $T:ty, $high:expr/*, $incr:expr*/) => {{
        let mut g = $c.benchmark_group(concat!("uniform_simd_", stringify!($T)));
        let inputs = &[("high_reject", $high), ("low_reject", (-1, 2))];

        bench_simd_group!("Old", $T, sample_single_inclusive, g, inputs);
        bench_simd_group!("Canon", $T, sample_single_inclusive_canon, g, inputs);
        bench_simd_group!(
            "Canon-branchless",
            $T,
            sample_single_inclusive_canon_branchless,
            g,
            inputs
        );
        bench_simd_group!("Canon-scalar", $T, sample_inclusive_canon_scalar, g, inputs);
        bench_simd_group!("Bitmask", $T, sample_single_inclusive_bitmask, g, inputs);
    }};
}

#[cfg(feature = "simd_support")]
fn uniform_simd(c: &mut Criterion) {
    // for i8/i16, we use 32-bit integers internally so rejection is most common near full-size
    // the exact values were determined with an exhaustive search
    bench_simd!(c, i8x2, (i8::MIN, 116));
    bench_simd!(c, i8x4, (i8::MIN, 116));
    bench_simd!(c, i8x8, (i8::MIN, 116));
    bench_simd!(c, i8x16, (i8::MIN, 116));
    bench_simd!(c, i8x32, (i8::MIN, 116));
    bench_simd!(c, i8x64, (i8::MIN, 116));
    bench_simd!(c, i16x8, (i16::MIN, 32407));
    bench_simd!(c, i16x16, (i16::MIN, 32407));
    bench_simd!(c, i32x4, (i32::MIN, 1));
    bench_simd!(c, i32x8, (i32::MIN, 1));
    bench_simd!(c, i64x2, (i64::MIN, 1));
    bench_simd!(c, i64x4, (i64::MIN, 1));
    bench_simd!(c, i64x8, (i64::MIN, 1));
    bench_simd!(c, i128x2, (i128::MIN, 1));
    bench_simd!(c, i128x4, (i128::MIN, 1));
}

#[cfg(not(feature = "simd_support"))]
fn uniform_simd(_c: &mut Criterion) {}

criterion_group! {
    name = benches;
    config = Criterion::default();
    targets = uniform_int, uniform_simd
}
criterion_main!(benches);
