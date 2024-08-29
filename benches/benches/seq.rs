// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(test)]
#![allow(non_snake_case)]

extern crate test;

use test::Bencher;

use rand::prelude::*;

// We force use of 32-bit RNG since seq code is optimised for use with 32-bit
// generators on all platforms.
use rand_pcg::Pcg32 as SmallRng;

macro_rules! seq_slice_choose_multiple {
    ($name:ident, $amount:expr, $length:expr) => {
        #[bench]
        fn $name(b: &mut Bencher) {
            let mut rng = SmallRng::from_rng(thread_rng());
            let x: &[i32] = &[$amount; $length];
            let mut result = [0i32; $amount];
            b.iter(|| {
                // Collect full result to prevent unwanted shortcuts getting
                // first element (in case sample_indices returns an iterator).
                for (slot, sample) in result.iter_mut().zip(x.choose_multiple(&mut rng, $amount)) {
                    *slot = *sample;
                }
                result[$amount - 1]
            })
        }
    };
}

seq_slice_choose_multiple!(seq_slice_choose_multiple_1_of_1000, 1, 1000);
seq_slice_choose_multiple!(seq_slice_choose_multiple_950_of_1000, 950, 1000);
seq_slice_choose_multiple!(seq_slice_choose_multiple_10_of_100, 10, 100);
seq_slice_choose_multiple!(seq_slice_choose_multiple_90_of_100, 90, 100);

#[bench]
fn seq_iter_choose_multiple_10_of_100(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(thread_rng());
    let x: &[usize] = &[1; 100];
    b.iter(|| x.iter().cloned().choose_multiple(&mut rng, 10))
}

#[bench]
fn seq_iter_choose_multiple_fill_10_of_100(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(thread_rng());
    let x: &[usize] = &[1; 100];
    let mut buf = [0; 10];
    b.iter(|| x.iter().cloned().choose_multiple_fill(&mut rng, &mut buf))
}
