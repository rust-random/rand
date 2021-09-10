// Copyright 2018-2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(custom_inner_attributes)]

// Rustfmt splits macro invocations to shorten lines; in this case longer-lines are more readable
#![rustfmt::skip]

const RAND_BENCH_N: u64 = 1000;

use criterion::{criterion_group, criterion_main, Criterion,
    Throughput};
use criterion_cycles_per_byte::CyclesPerByte;

use core::mem::size_of;

use rand::prelude::*;
use rand_distr::*;

// At this time, distributions are optimised for 64-bit platforms.
use rand_pcg::Pcg64Mcg;

macro_rules! distr_int {
    ($group:ident, $fnn:expr, $ty:ty, $distr:expr) => {
        $group.throughput(Throughput::Bytes(
            size_of::<$ty>() as u64 * RAND_BENCH_N));
        $group.bench_function($fnn, |c| {
            let mut rng = Pcg64Mcg::from_entropy();
            let distr = $distr;

            c.iter(|| {
                let mut accum: $ty = 0;
                for _ in 0..RAND_BENCH_N {
                    let x: $ty = distr.sample(&mut rng);
                    accum = accum.wrapping_add(x);
                }
                accum
            });
        });
    };
}

macro_rules! distr_float {
    ($group:ident, $fnn:expr, $ty:ty, $distr:expr) => {
        $group.throughput(Throughput::Bytes(
            size_of::<$ty>() as u64 * RAND_BENCH_N));
        $group.bench_function($fnn, |c| {
            let mut rng = Pcg64Mcg::from_entropy();
            let distr = $distr;

            c.iter(|| {
                let mut accum = 0.;
                for _ in 0..RAND_BENCH_N {
                    let x: $ty = distr.sample(&mut rng);
                    accum += x;
                }
                accum
            });
        });
    };
}

macro_rules! distr {
    ($group:ident, $fnn:expr, $ty:ty, $distr:expr) => {
        $group.throughput(Throughput::Bytes(
            size_of::<$ty>() as u64 * RAND_BENCH_N));
        $group.bench_function($fnn, |c| {
            let mut rng = Pcg64Mcg::from_entropy();
            let distr = $distr;

            c.iter(|| {
                let mut accum: u32 = 0;
                for _ in 0..RAND_BENCH_N {
                    let x: $ty = distr.sample(&mut rng);
                    accum = accum.wrapping_add(x as u32);
                }
                accum
            });
        });
    };
}

macro_rules! distr_arr {
    ($group:ident, $fnn:expr, $ty:ty, $distr:expr) => {
        $group.throughput(Throughput::Bytes(
            size_of::<$ty>() as u64 * RAND_BENCH_N));
        $group.bench_function($fnn, |c| {
            let mut rng = Pcg64Mcg::from_entropy();
            let distr = $distr;

            c.iter(|| {
                let mut accum: u32 = 0;
                for _ in 0..RAND_BENCH_N {
                    let x: $ty = distr.sample(&mut rng);
                    accum = accum.wrapping_add(x[0] as u32);
                }
                accum
            });
        });
    };
}

macro_rules! sample_binomial {
    ($group:ident, $name:expr, $n:expr, $p:expr) => {
        distr_int!($group, $name, u64, Binomial::new($n, $p).unwrap())
    };
}

fn bench(c: &mut Criterion<CyclesPerByte>) {
    {
    let mut g = c.benchmark_group("exp");
    distr_float!(g, "exp", f64, Exp::new(1.23 * 4.56).unwrap());
    distr_float!(g, "exp1_specialized", f64, Exp1);
    distr_float!(g, "exp1_general", f64, Exp::new(1.).unwrap());
    }

    {
    let mut g = c.benchmark_group("normal");
    distr_float!(g, "normal", f64, Normal::new(-1.23, 4.56).unwrap());
    distr_float!(g, "standardnormal_specialized", f64, StandardNormal);
    distr_float!(g, "standardnormal_general", f64, Normal::new(0., 1.).unwrap());
    distr_float!(g, "log_normal", f64, LogNormal::new(-1.23, 4.56).unwrap());
    g.throughput(Throughput::Bytes(size_of::<f64>() as u64 * RAND_BENCH_N));
    g.bench_function("iter", |c| {
        let mut rng = Pcg64Mcg::from_entropy();
        let distr = Normal::new(-2.71828, 3.14159).unwrap();
        let mut iter = distr.sample_iter(&mut rng);

        c.iter(|| {
            let mut accum = 0.0;
            for _ in 0..RAND_BENCH_N {
                accum += iter.next().unwrap();
            }
            accum
        });
    });
    }

    {
    let mut g = c.benchmark_group("skew_normal");
    distr_float!(g, "shape_zero", f64, SkewNormal::new(0.0, 1.0, 0.0).unwrap());
    distr_float!(g, "shape_positive", f64, SkewNormal::new(0.0, 1.0, 100.0).unwrap());
    distr_float!(g, "shape_negative", f64, SkewNormal::new(0.0, 1.0, -100.0).unwrap());
    }

    {
    let mut g = c.benchmark_group("gamma");
    distr_float!(g, "gamma_large_shape", f64, Gamma::new(10., 1.0).unwrap());
    distr_float!(g, "gamma_small_shape", f64, Gamma::new(0.1, 1.0).unwrap());
    distr_float!(g, "beta_small_param", f64, Beta::new(0.1, 0.1).unwrap());
    distr_float!(g, "beta_large_param_similar", f64, Beta::new(101., 95.).unwrap());
    distr_float!(g, "beta_large_param_different", f64, Beta::new(10., 1000.).unwrap());
    distr_float!(g, "beta_mixed_param", f64, Beta::new(0.5, 100.).unwrap());
    }

    {
    let mut g = c.benchmark_group("cauchy");
    distr_float!(g, "cauchy", f64, Cauchy::new(4.2, 6.9).unwrap());
    }

    {
    let mut g = c.benchmark_group("triangular");
    distr_float!(g, "triangular", f64, Triangular::new(0., 1., 0.9).unwrap());
    }

    {
    let mut g = c.benchmark_group("geometric");
    distr_int!(g, "geometric", u64, Geometric::new(0.5).unwrap());
    distr_int!(g, "standard_geometric", u64, StandardGeometric);
    }

    {
    let mut g = c.benchmark_group("weighted");
    distr_int!(g, "weighted_i8", usize, WeightedIndex::new(&[1i8, 2, 3, 4, 12, 0, 2, 1]).unwrap());
    distr_int!(g, "weighted_u32", usize, WeightedIndex::new(&[1u32, 2, 3, 4, 12, 0, 2, 1]).unwrap());
    distr_int!(g, "weighted_f64", usize, WeightedIndex::new(&[1.0f64, 0.001, 1.0/3.0, 4.01, 0.0, 3.3, 22.0, 0.001]).unwrap());
    distr_int!(g, "weighted_large_set", usize, WeightedIndex::new((0..10000).rev().chain(1..10001)).unwrap());
    distr_int!(g, "weighted_alias_method_i8", usize, WeightedAliasIndex::new(vec![1i8, 2, 3, 4, 12, 0, 2, 1]).unwrap());
    distr_int!(g, "weighted_alias_method_u32", usize, WeightedAliasIndex::new(vec![1u32, 2, 3, 4, 12, 0, 2, 1]).unwrap());
    distr_int!(g, "weighted_alias_method_f64", usize, WeightedAliasIndex::new(vec![1.0f64, 0.001, 1.0/3.0, 4.01, 0.0, 3.3, 22.0, 0.001]).unwrap());
    distr_int!(g, "weighted_alias_method_large_set", usize, WeightedAliasIndex::new((0..10000).rev().chain(1..10001).collect()).unwrap());
    }

    {
    let mut g = c.benchmark_group("binomial");
    sample_binomial!(g, "binomial", 20, 0.7);
    sample_binomial!(g, "binomial_small", 1_000_000, 1e-30);
    sample_binomial!(g, "binomial_1", 1, 0.9);
    sample_binomial!(g, "binomial_10", 10, 0.9);
    sample_binomial!(g, "binomial_100", 100, 0.99);
    sample_binomial!(g, "binomial_1000", 1000, 0.01);
    sample_binomial!(g, "binomial_1e12", 1000_000_000_000, 0.2);
    }

    {
    let mut g = c.benchmark_group("poisson");
    distr_float!(g, "poisson", f64, Poisson::new(4.0).unwrap());
    }

    {
    let mut g = c.benchmark_group("zipf");
    distr_float!(g, "zipf", f64, Zipf::new(10, 1.5).unwrap());
    distr_float!(g, "zeta", f64, Zeta::new(1.5).unwrap());
    }

    {
    let mut g = c.benchmark_group("bernoulli");
    distr!(g, "bernoulli", bool, Bernoulli::new(0.18).unwrap());
    }

    {
    let mut g = c.benchmark_group("circle");
    distr_arr!(g, "circle", [f64; 2], UnitCircle);
    }

    {
    let mut g = c.benchmark_group("sphere");
    distr_arr!(g, "sphere", [f64; 3], UnitSphere);
    }
}

criterion_group!(
    name = benches;
    config = Criterion::default().with_measurement(CyclesPerByte);
    targets = bench
);
criterion_main!(benches);
