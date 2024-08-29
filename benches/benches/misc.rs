// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(test)]

extern crate test;

const RAND_BENCH_N: u64 = 1000;

use test::Bencher;

use rand::distr::Bernoulli;
use rand::prelude::*;
use rand_pcg::Pcg32;

#[bench]
fn misc_gen_bool_const(b: &mut Bencher) {
    let mut rng = Pcg32::from_rng(&mut thread_rng());
    b.iter(|| {
        let mut accum = true;
        for _ in 0..RAND_BENCH_N {
            accum ^= rng.gen_bool(0.18);
        }
        accum
    })
}

#[bench]
fn misc_gen_bool_var(b: &mut Bencher) {
    let mut rng = Pcg32::from_rng(&mut thread_rng());
    b.iter(|| {
        let mut accum = true;
        let mut p = 0.18;
        for _ in 0..RAND_BENCH_N {
            accum ^= rng.gen_bool(p);
            p += 0.0001;
        }
        accum
    })
}

#[bench]
fn misc_gen_ratio_const(b: &mut Bencher) {
    let mut rng = Pcg32::from_rng(&mut thread_rng());
    b.iter(|| {
        let mut accum = true;
        for _ in 0..RAND_BENCH_N {
            accum ^= rng.gen_ratio(2, 3);
        }
        accum
    })
}

#[bench]
fn misc_gen_ratio_var(b: &mut Bencher) {
    let mut rng = Pcg32::from_rng(&mut thread_rng());
    b.iter(|| {
        let mut accum = true;
        for i in 2..(RAND_BENCH_N as u32 + 2) {
            accum ^= rng.gen_ratio(i, i + 1);
        }
        accum
    })
}

#[bench]
fn misc_bernoulli_const(b: &mut Bencher) {
    let mut rng = Pcg32::from_rng(&mut thread_rng());
    b.iter(|| {
        let d = Bernoulli::new(0.18).unwrap();
        let mut accum = true;
        for _ in 0..RAND_BENCH_N {
            accum ^= rng.sample(d);
        }
        accum
    })
}

#[bench]
fn misc_bernoulli_var(b: &mut Bencher) {
    let mut rng = Pcg32::from_rng(&mut thread_rng());
    b.iter(|| {
        let mut accum = true;
        let mut p = 0.18;
        for _ in 0..RAND_BENCH_N {
            let d = Bernoulli::new(p).unwrap();
            accum ^= rng.sample(d);
            p += 0.0001;
        }
        accum
    })
}
