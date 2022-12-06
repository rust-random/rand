// Copyright 2018-2022 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(test)]
#![allow(non_snake_case)]
#![feature(custom_inner_attributes)]
#![rustfmt::skip]
extern crate test;

use test::Bencher;

use core::mem::size_of;
use rand::prelude::*;
use rand::seq::*;

// We force use of 32-bit RNG since seq code is optimised for use with 32-bit
// generators on all platforms.
use rand_chacha::ChaCha20Rng as CryptoRng;
use rand_pcg::Pcg32 as SmallRng;

const RAND_BENCH_N: u64 = 1000;

macro_rules! bench_seq_shuffle {
    ($name:ident,$rng:ident, $fn:ident,  $length:expr) => {
        #[bench]
        fn $name(b: &mut Bencher) {
            let mut rng = $rng::from_rng(thread_rng()).unwrap();
            let x: &mut [usize] = &mut [1; $length];
            b.iter(|| {
                x.$fn(&mut rng);
                x[0]
            })
        }
    };
}

macro_rules! bench_partial_seq_shuffle {
    ($name:ident,$rng:ident, $fn:ident,  $length:expr, $amount:expr) => {
        #[bench]
        fn $name(b: &mut Bencher) {
            let mut rng = $rng::from_rng(thread_rng()).unwrap();
            let x: &mut [usize] = &mut [1; $length];
            b.iter(|| {
                let r = x.$fn(&mut rng, $amount);
                r.0[0]
            })
        }
    };
}

bench_seq_shuffle!(bench_seq_shuffle_10000_crypto, CryptoRng, shuffle, 10000);
bench_seq_shuffle!(bench_seq_shuffle_10000_small_, SmallRng, shuffle, 10000);
bench_seq_shuffle!(bench_seq_shuffle_1000__crypto, CryptoRng, shuffle, 1000);
bench_seq_shuffle!(bench_seq_shuffle_1000__small_, SmallRng, shuffle, 1000);
bench_seq_shuffle!(bench_seq_shuffle_100__crypto, CryptoRng, shuffle, 100);
bench_seq_shuffle!(bench_seq_shuffle_100__small_, SmallRng, shuffle, 100);
bench_seq_shuffle!(bench_seq_shuffle_10____crypto, CryptoRng, shuffle, 10);
bench_seq_shuffle!(bench_seq_shuffle_10____small_, SmallRng, shuffle, 10);
bench_seq_shuffle!(bench_seq_shuffle__1____crypto, CryptoRng, shuffle, 1);
bench_seq_shuffle!(bench_seq_shuffle__1____small_, SmallRng, shuffle, 1);
bench_seq_shuffle!(bench_seq_shuffle__2____crypto, CryptoRng, shuffle, 2);
bench_seq_shuffle!(bench_seq_shuffle__2____small_, SmallRng, shuffle, 2);
bench_seq_shuffle!(bench_seq_shuffle__3____crypto, CryptoRng, shuffle, 3);
bench_seq_shuffle!(bench_seq_shuffle__3____small_, SmallRng, shuffle, 3);
bench_partial_seq_shuffle!(bench_partial_seq_shuffle_10000_crypto, CryptoRng, partial_shuffle, 10000, 5000);
bench_partial_seq_shuffle!(bench_partial_seq_shuffle_10000_small_, SmallRng, partial_shuffle, 10000, 5000);
bench_partial_seq_shuffle!(bench_partial_seq_shuffle_1000__crypto, CryptoRng, partial_shuffle, 1000, 500);
bench_partial_seq_shuffle!(bench_partial_seq_shuffle_1000__small_, SmallRng, partial_shuffle, 1000, 500);
bench_partial_seq_shuffle!(bench_partial_seq_shuffle_100__crypto, CryptoRng, partial_shuffle, 100, 50);
bench_partial_seq_shuffle!(bench_partial_seq_shuffle_100__small_, SmallRng, partial_shuffle, 100, 50);
bench_partial_seq_shuffle!(bench_partial_seq_shuffle_10____crypto, CryptoRng, partial_shuffle, 10, 5);
bench_partial_seq_shuffle!(bench_partial_seq_shuffle_10____small_, SmallRng, partial_shuffle, 10, 5);
