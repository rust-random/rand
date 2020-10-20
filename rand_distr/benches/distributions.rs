// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(custom_inner_attributes)]
#![feature(test)]

// Rustfmt splits macro invocations to shorten lines; in this case longer-lines are more readable
#![rustfmt::skip]

extern crate test;

const RAND_BENCH_N: u64 = 1000;

use std::mem::size_of;
use test::Bencher;

use rand::prelude::*;
use rand_distr::*;

// At this time, distributions are optimised for 64-bit platforms.
use rand_pcg::Pcg64Mcg;

macro_rules! distr_int {
    ($fnn:ident, $ty:ty, $distr:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = Pcg64Mcg::from_entropy();
            let distr = $distr;

            b.iter(|| {
                let mut accum = 0 as $ty;
                for _ in 0..RAND_BENCH_N {
                    let x: $ty = distr.sample(&mut rng);
                    accum = accum.wrapping_add(x);
                }
                accum
            });
            b.bytes = size_of::<$ty>() as u64 * RAND_BENCH_N;
        }
    };
}

macro_rules! distr_float {
    ($fnn:ident, $ty:ty, $distr:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = Pcg64Mcg::from_entropy();
            let distr = $distr;

            b.iter(|| {
                let mut accum = 0.0;
                for _ in 0..RAND_BENCH_N {
                    let x: $ty = distr.sample(&mut rng);
                    accum += x;
                }
                accum
            });
            b.bytes = size_of::<$ty>() as u64 * RAND_BENCH_N;
        }
    };
}

macro_rules! distr {
    ($fnn:ident, $ty:ty, $distr:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = Pcg64Mcg::from_entropy();
            let distr = $distr;

            b.iter(|| {
                let mut accum = 0u32;
                for _ in 0..RAND_BENCH_N {
                    let x: $ty = distr.sample(&mut rng);
                    accum = accum.wrapping_add(x as u32);
                }
                accum
            });
            b.bytes = size_of::<$ty>() as u64 * RAND_BENCH_N;
        }
    };
}

macro_rules! distr_arr {
    ($fnn:ident, $ty:ty, $distr:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = Pcg64Mcg::from_entropy();
            let distr = $distr;

            b.iter(|| {
                let mut accum = 0u32;
                for _ in 0..RAND_BENCH_N {
                    let x: $ty = distr.sample(&mut rng);
                    accum = accum.wrapping_add(x[0] as u32);
                }
                accum
            });
            b.bytes = size_of::<$ty>() as u64 * RAND_BENCH_N;
        }
    };
}


// distributions
distr_float!(distr_exp, f64, Exp::new(1.23 * 4.56).unwrap());
distr_float!(distr_normal, f64, Normal::new(-1.23, 4.56).unwrap());
distr_float!(distr_log_normal, f64, LogNormal::new(-1.23, 4.56).unwrap());
distr_float!(distr_gamma_large_shape, f64, Gamma::new(10., 1.0).unwrap());
distr_float!(distr_gamma_small_shape, f64, Gamma::new(0.1, 1.0).unwrap());
distr_float!(distr_beta_small_param, f64, Beta::new(0.1, 0.1).unwrap());
distr_float!(distr_beta_large_param_similar, f64, Beta::new(101., 95.).unwrap());
distr_float!(distr_beta_large_param_different, f64, Beta::new(10., 1000.).unwrap());
distr_float!(distr_beta_mixed_param, f64, Beta::new(0.5, 100.).unwrap());
distr_float!(distr_cauchy, f64, Cauchy::new(4.2, 6.9).unwrap());
distr_float!(distr_triangular, f64, Triangular::new(0., 1., 0.9).unwrap());
distr_int!(distr_binomial, u64, Binomial::new(20, 0.7).unwrap());
distr_int!(distr_binomial_small, u64, Binomial::new(1000000, 1e-30).unwrap());
distr_float!(distr_poisson, f64, Poisson::new(4.0).unwrap());
distr!(distr_bernoulli, bool, Bernoulli::new(0.18).unwrap());
distr_arr!(distr_circle, [f64; 2], UnitCircle);
distr_arr!(distr_sphere, [f64; 3], UnitSphere);

// Weighted
distr_int!(distr_weighted_i8, usize, WeightedIndex::new(&[1i8, 2, 3, 4, 12, 0, 2, 1]).unwrap());
distr_int!(distr_weighted_u32, usize, WeightedIndex::new(&[1u32, 2, 3, 4, 12, 0, 2, 1]).unwrap());
distr_int!(distr_weighted_f64, usize, WeightedIndex::new(&[1.0f64, 0.001, 1.0/3.0, 4.01, 0.0, 3.3, 22.0, 0.001]).unwrap());
distr_int!(distr_weighted_large_set, usize, WeightedIndex::new((0..10000).rev().chain(1..10001)).unwrap());

distr_int!(distr_weighted_alias_method_i8, usize, WeightedAliasIndex::new(vec![1i8, 2, 3, 4, 12, 0, 2, 1]).unwrap());
distr_int!(distr_weighted_alias_method_u32, usize, WeightedAliasIndex::new(vec![1u32, 2, 3, 4, 12, 0, 2, 1]).unwrap());
distr_int!(distr_weighted_alias_method_f64, usize, WeightedAliasIndex::new(vec![1.0f64, 0.001, 1.0/3.0, 4.01, 0.0, 3.3, 22.0, 0.001]).unwrap());
distr_int!(distr_weighted_alias_method_large_set, usize, WeightedAliasIndex::new((0..10000).rev().chain(1..10001).collect()).unwrap());


#[bench]
fn dist_iter(b: &mut Bencher) {
    let mut rng = Pcg64Mcg::from_entropy();
    let distr = Normal::new(-2.71828, 3.14159).unwrap();
    let mut iter = distr.sample_iter(&mut rng);

    b.iter(|| {
        let mut accum = 0.0;
        for _ in 0..RAND_BENCH_N {
            accum += iter.next().unwrap();
        }
        accum
    });
    b.bytes = size_of::<f64>() as u64 * RAND_BENCH_N;
}

macro_rules! sample_binomial {
    ($name:ident, $n:expr, $p:expr) => {
        #[bench]
        fn $name(b: &mut Bencher) {
            let mut rng = Pcg64Mcg::from_rng(&mut thread_rng()).unwrap();
            let (n, p) = ($n, $p);
            b.iter(|| {
                let d = Binomial::new(n, p).unwrap();
                rng.sample(d)
            })
        }
    };
}

sample_binomial!(misc_binomial_1, 1, 0.9);
sample_binomial!(misc_binomial_10, 10, 0.9);
sample_binomial!(misc_binomial_100, 100, 0.99);
sample_binomial!(misc_binomial_1000, 1000, 0.01);
sample_binomial!(misc_binomial_1e12, 1000_000_000_000, 0.2);
