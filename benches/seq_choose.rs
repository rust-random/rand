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
use core::mem::size_of;

// We force use of 32-bit RNG since seq code is optimised for use with 32-bit
// generators on all platforms.
use rand_chacha::ChaCha20Rng as CryptoRng;
use rand_pcg::Pcg32 as SmallRng;

const RAND_BENCH_N: u64 = 1000;


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

macro_rules! bench_seq_iter_size_hinted {
    ($name:ident, $rng:ident, $fn:ident, $length:expr) => {
        #[bench]
        fn $name(b: &mut Bencher) {
            let mut rng = $rng::from_rng(thread_rng()).unwrap();
            let x: &mut [usize] = &mut [1; $length];
            for (i, r) in x.iter_mut().enumerate() {
                *r = i;
            }
            b.iter(|| {
                let mut s = 0;
                for _ in 0..RAND_BENCH_N {
                    s += x.iter().$fn(&mut rng).unwrap();
                }
                s
            });
            b.bytes = size_of::<usize>() as u64 * crate::RAND_BENCH_N;
        }
    };
}

macro_rules! bench_seq_iter_unhinted {
    ($name:ident,$rng:ident, $fn:ident,  $length:expr) => {
        #[bench]
        fn $name(b: &mut Bencher) {
            let mut rng = $rng::from_rng(thread_rng()).unwrap();
            let x: &[usize] = &[1; $length];
            b.iter(|| UnhintedIterator { iter: x.iter() }.$fn(&mut rng).unwrap())
        }
    };
}

macro_rules! bench_seq_iter_window_hinted {
    ($name:ident,$rng:ident, $fn:ident,  $length:expr) => {
        #[bench]
        fn $name(b: &mut Bencher) {
            let mut rng = $rng::from_rng(thread_rng()).unwrap();
            let x: &[usize] = &[1; $length];
            b.iter(|| {
                WindowHintedIterator {
                    iter: x.iter(),
                    window_size: 7,
                }
                .$fn(&mut rng)
                .unwrap()
            })
        }
    };
}

//Size Hinted
bench_seq_iter_size_hinted!(
    seq_iter_size_hinted_choose_from_10000_cryptoRng,
    CryptoRng,
    choose,
    10000
);
bench_seq_iter_size_hinted!(
    seq_iter_size_hinted_choose_from_10000_smallRng,
    SmallRng,
    choose,
    10000
);
bench_seq_iter_size_hinted!(
    seq_iter_size_hinted_choose_from_1000_cryptoRng,
    CryptoRng,
    choose,
    1000
);
bench_seq_iter_size_hinted!(
    seq_iter_size_hinted_choose_from_1000_smallRng,
    SmallRng,
    choose,
    1000
);
bench_seq_iter_size_hinted!(
    seq_iter_size_hinted_choose_from_100_cryptoRng,
    CryptoRng,
    choose,
    100
);
bench_seq_iter_size_hinted!(
    seq_iter_size_hinted_choose_from_100_smallRng,
    SmallRng,
    choose,
    100
);
bench_seq_iter_size_hinted!(
    seq_iter_size_hinted_choose_from_10_smallRng,
    SmallRng,
    choose,
    10
);
bench_seq_iter_size_hinted!(
    seq_iter_size_hinted_choose_from_10_cryptoRng,
    CryptoRng,
    choose,
    10
);

//Unhinted
bench_seq_iter_unhinted!(
    seq_iter_unhinted_choose_from_10000_cryptoRng,
    CryptoRng,
    choose,
    10000
);
bench_seq_iter_unhinted!(
    seq_iter_unhinted_choose_from_10000_smallRng,
    SmallRng,
    choose,
    10000
);
bench_seq_iter_unhinted!(
    seq_iter_unhinted_choose_from_1000_cryptoRng,
    CryptoRng,
    choose,
    1000
);
bench_seq_iter_unhinted!(
    seq_iter_unhinted_choose_from_1000_smallRng,
    SmallRng,
    choose,
    1000
);
bench_seq_iter_unhinted!(
    seq_iter_unhinted_choose_from_100_cryptoRng,
    CryptoRng,
    choose,
    100
);
bench_seq_iter_unhinted!(
    seq_iter_unhinted_choose_from_100_smallRng,
    SmallRng,
    choose,
    100
);
bench_seq_iter_unhinted!(
    seq_iter_unhinted_choose_from_10_smallRng,
    SmallRng,
    choose,
    10
);
bench_seq_iter_unhinted!(
    seq_iter_unhinted_choose_from_10_cryptoRng,
    CryptoRng,
    choose,
    10
);

// Window hinted
bench_seq_iter_window_hinted!(
    seq_iter_window_hinted_choose_from_10000_cryptoRng,
    CryptoRng,
    choose,
    10000
);
bench_seq_iter_window_hinted!(
    seq_iter_window_hinted_choose_from_10000_smallRng,
    SmallRng,
    choose,
    10000
);
bench_seq_iter_window_hinted!(
    seq_iter_window_hinted_choose_from_1000_cryptoRng,
    CryptoRng,
    choose,
    1000
);
bench_seq_iter_window_hinted!(
    seq_iter_window_hinted_choose_from_1000_smallRng,
    SmallRng,
    choose,
    1000
);

bench_seq_iter_window_hinted!(
    seq_iter_window_hinted_choose_from_100_cryptoRng,
    CryptoRng,
    choose,
    100
);
bench_seq_iter_window_hinted!(
    seq_iter_window_hinted_choose_from_100_smallRng,
    SmallRng,
    choose,
    100
);
bench_seq_iter_window_hinted!(
    seq_iter_window_hinted_choose_from_10_smallRng,
    SmallRng,
    choose,
    10
);
bench_seq_iter_window_hinted!(
    seq_iter_window_hinted_choose_from_10_cryptoRng,
    CryptoRng,
    choose,
    10
);

//Choose Stable
bench_seq_iter_unhinted!(
    seq_iter_unhinted_choose_stable_from_10000_cryptoRng,
    CryptoRng,
    choose_stable,
    10000
);
bench_seq_iter_unhinted!(
    seq_iter_unhinted_choose_stable_from_10000_smallRng,
    SmallRng,
    choose_stable,
    10000
);
bench_seq_iter_unhinted!(
    seq_iter_unhinted_choose_stable_from_1000_cryptoRng,
    CryptoRng,
    choose_stable,
    1000
);
bench_seq_iter_unhinted!(
    seq_iter_unhinted_choose_stable_from_1000_smallRng,
    SmallRng,
    choose_stable,
    1000
);
bench_seq_iter_unhinted!(
    seq_iter_unhinted_choose_stable_from_100_cryptoRng,
    CryptoRng,
    choose_stable,
    100
);
bench_seq_iter_unhinted!(
    seq_iter_unhinted_choose_stable_from_100_smallRng,
    SmallRng,
    choose_stable,
    100
);
bench_seq_iter_unhinted!(
    seq_iter_unhinted_choose_stable_from_10_smallRng,
    SmallRng,
    choose_stable,
    10
);
bench_seq_iter_unhinted!(
    seq_iter_unhinted_choose_stable_from_10_cryptoRng,
    CryptoRng,
    choose_stable,
    10
);

// Window hinted
bench_seq_iter_unhinted!(
    seq_iter_stable_choose_from_10000_cryptoRng,
    CryptoRng,
    choose_stable,
    10000
);
bench_seq_iter_unhinted!(
    seq_iter_stable_choose_from_10000_smallRng,
    SmallRng,
    choose_stable,
    10000
);
bench_seq_iter_unhinted!(
    seq_iter_stable_choose_from_1000_cryptoRng,
    CryptoRng,
    choose_stable,
    1000
);
bench_seq_iter_unhinted!(
    seq_iter_stable_choose_from_1000_smallRng,
    SmallRng,
    choose_stable,
    1000
);
bench_seq_iter_unhinted!(
    seq_iter_stable_choose_from_100_cryptoRng,
    CryptoRng,
    choose_stable,
    100
);
bench_seq_iter_unhinted!(
    seq_iter_stable_choose_from_100_smallRng,
    SmallRng,
    choose_stable,
    100
);
bench_seq_iter_unhinted!(
    seq_iter_stable_choose_from_10_smallRng,
    SmallRng,
    choose_stable,
    10
);
bench_seq_iter_unhinted!(
    seq_iter_stable_choose_from_10_cryptoRng,
    CryptoRng,
    choose_stable,
    10
);

