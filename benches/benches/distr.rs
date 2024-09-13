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

use criterion::{criterion_group, criterion_main, Criterion, Throughput};
use criterion_cycles_per_byte::CyclesPerByte;

use rand::prelude::*;
use rand_distr::*;

// At this time, distributions are optimised for 64-bit platforms.
use rand_pcg::Pcg64Mcg;

const ITER_ELTS: u64 = 100;

macro_rules! distr_int {
    ($group:ident, $fnn:expr, $ty:ty, $distr:expr) => {
        $group.bench_function($fnn, |c| {
            let mut rng = Pcg64Mcg::from_os_rng();
            let distr = $distr;

            c.iter(|| distr.sample(&mut rng));
        });
    };
}

macro_rules! distr_float {
    ($group:ident, $fnn:expr, $ty:ty, $distr:expr) => {
        $group.bench_function($fnn, |c| {
            let mut rng = Pcg64Mcg::from_os_rng();
            let distr = $distr;

            c.iter(|| Distribution::<$ty>::sample(&distr, &mut rng));
        });
    };
}

macro_rules! distr_arr {
    ($group:ident, $fnn:expr, $ty:ty, $distr:expr) => {
        $group.bench_function($fnn, |c| {
            let mut rng = Pcg64Mcg::from_os_rng();
            let distr = $distr;

            c.iter(|| Distribution::<$ty>::sample(&distr, &mut rng));
        });
    };
}

macro_rules! sample_binomial {
    ($group:ident, $name:expr, $n:expr, $p:expr) => {
        distr_int!($group, $name, u64, Binomial::new($n, $p).unwrap())
    };
}

fn bench(c: &mut Criterion<CyclesPerByte>) {
    let mut g = c.benchmark_group("exp");
    distr_float!(g, "exp", f64, Exp::new(1.23 * 4.56).unwrap());
    distr_float!(g, "exp1_specialized", f64, Exp1);
    distr_float!(g, "exp1_general", f64, Exp::new(1.).unwrap());
    g.finish();

    let mut g = c.benchmark_group("normal");
    distr_float!(g, "normal", f64, Normal::new(-1.23, 4.56).unwrap());
    distr_float!(g, "standardnormal_specialized", f64, StandardNormal);
    distr_float!(g, "standardnormal_general", f64, Normal::new(0., 1.).unwrap());
    distr_float!(g, "log_normal", f64, LogNormal::new(-1.23, 4.56).unwrap());
    g.throughput(Throughput::Elements(ITER_ELTS));
    g.bench_function("iter", |c| {
        use core::f64::consts::{E, PI};
        let mut rng = Pcg64Mcg::from_os_rng();
        let distr = Normal::new(-E, PI).unwrap();

        c.iter(|| {
            distr.sample_iter(&mut rng)
                .take(ITER_ELTS as usize)
                .fold(0.0, |a, r| a + r)
        });
    });
    g.finish();

    let mut g = c.benchmark_group("skew_normal");
    distr_float!(g, "shape_zero", f64, SkewNormal::new(0.0, 1.0, 0.0).unwrap());
    distr_float!(g, "shape_positive", f64, SkewNormal::new(0.0, 1.0, 100.0).unwrap());
    distr_float!(g, "shape_negative", f64, SkewNormal::new(0.0, 1.0, -100.0).unwrap());
    g.finish();

    let mut g = c.benchmark_group("gamma");
    distr_float!(g, "large_shape", f64, Gamma::new(10., 1.0).unwrap());
    distr_float!(g, "small_shape", f64, Gamma::new(0.1, 1.0).unwrap());
    g.finish();

    let mut g = c.benchmark_group("beta");
    distr_float!(g, "small_param", f64, Beta::new(0.1, 0.1).unwrap());
    distr_float!(g, "large_param_similar", f64, Beta::new(101., 95.).unwrap());
    distr_float!(g, "large_param_different", f64, Beta::new(10., 1000.).unwrap());
    distr_float!(g, "mixed_param", f64, Beta::new(0.5, 100.).unwrap());
    g.finish();

    let mut g = c.benchmark_group("cauchy");
    distr_float!(g, "cauchy", f64, Cauchy::new(4.2, 6.9).unwrap());
    g.finish();

    let mut g = c.benchmark_group("triangular");
    distr_float!(g, "triangular", f64, Triangular::new(0., 1., 0.9).unwrap());
    g.finish();

    let mut g = c.benchmark_group("geometric");
    distr_int!(g, "geometric", u64, Geometric::new(0.5).unwrap());
    distr_int!(g, "standard_geometric", u64, StandardGeometric);
    g.finish();

    let mut g = c.benchmark_group("weighted");
    distr_int!(g, "i8", usize, WeightedIndex::new([1i8, 2, 3, 4, 12, 0, 2, 1]).unwrap());
    distr_int!(g, "u32", usize, WeightedIndex::new([1u32, 2, 3, 4, 12, 0, 2, 1]).unwrap());
    distr_int!(g, "f64", usize, WeightedIndex::new([1.0f64, 0.001, 1.0/3.0, 4.01, 0.0, 3.3, 22.0, 0.001]).unwrap());
    distr_int!(g, "large_set", usize, WeightedIndex::new((0..10000).rev().chain(1..10001)).unwrap());
    distr_int!(g, "alias_method_i8", usize, WeightedAliasIndex::new(vec![1i8, 2, 3, 4, 12, 0, 2, 1]).unwrap());
    distr_int!(g, "alias_method_u32", usize, WeightedAliasIndex::new(vec![1u32, 2, 3, 4, 12, 0, 2, 1]).unwrap());
    distr_int!(g, "alias_method_f64", usize, WeightedAliasIndex::new(vec![1.0f64, 0.001, 1.0/3.0, 4.01, 0.0, 3.3, 22.0, 0.001]).unwrap());
    distr_int!(g, "alias_method_large_set", usize, WeightedAliasIndex::new((0..10000).rev().chain(1..10001).collect()).unwrap());
    g.finish();

    let mut g = c.benchmark_group("binomial");
    sample_binomial!(g, "small", 1_000_000, 1e-30);
    sample_binomial!(g, "1", 1, 0.9);
    sample_binomial!(g, "10", 10, 0.9);
    sample_binomial!(g, "100", 100, 0.99);
    sample_binomial!(g, "1000", 1000, 0.01);
    sample_binomial!(g, "1e12", 1_000_000_000_000, 0.2);
    g.finish();

    let mut g = c.benchmark_group("poisson");
    for lambda in [1f64, 4.0, 10.0, 100.0].into_iter() {
        let name = format!("{lambda}");
        distr_float!(g, name, f64, Poisson::new(lambda).unwrap());
    }
    g.throughput(Throughput::Elements(ITER_ELTS));
    g.bench_function("variable", |c| {
        let mut rng = Pcg64Mcg::from_os_rng();
        let ldistr = Uniform::new(0.1, 10.0).unwrap();

        c.iter(|| {
            let l = rng.sample(ldistr);
            let distr = Poisson::new(l * l).unwrap();
            Distribution::<f64>::sample_iter(&distr, &mut rng)
                .take(ITER_ELTS as usize)
                .fold(0.0, |a, r| a + r)
        })
    });
    g.finish();

    let mut g = c.benchmark_group("zipf");
    distr_float!(g, "zipf", f64, Zipf::new(10, 1.5).unwrap());
    distr_float!(g, "zeta", f64, Zeta::new(1.5).unwrap());
    g.finish();

    let mut g = c.benchmark_group("bernoulli");
    g.bench_function("bernoulli", |c| {
        let mut rng = Pcg64Mcg::from_os_rng();
        let distr = Bernoulli::new(0.18).unwrap();
        c.iter(|| distr.sample(&mut rng))
    });
    g.finish();

    let mut g = c.benchmark_group("unit");
    distr_arr!(g, "circle", [f64; 2], UnitCircle);
    distr_arr!(g, "sphere", [f64; 3], UnitSphere);
    g.finish();
}

criterion_group!(
    name = benches;
    config = Criterion::default().with_measurement(CyclesPerByte)
        .warm_up_time(core::time::Duration::from_secs(1))
        .measurement_time(core::time::Duration::from_secs(2));
    targets = bench
);
criterion_main!(benches);
