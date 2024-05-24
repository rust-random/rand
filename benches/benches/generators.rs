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

const RAND_BENCH_N: u64 = 1000;
const BYTES_LEN: usize = 1024;

use core::mem::size_of;
use rand_chacha::rand_core::UnwrapErr;
use test::{black_box, Bencher};

use rand::prelude::*;
use rand::rngs::ReseedingRng;
use rand::rngs::{mock::StepRng, OsRng};
use rand_chacha::{ChaCha12Rng, ChaCha20Core, ChaCha20Rng, ChaCha8Rng};
use rand_pcg::{Pcg32, Pcg64, Pcg64Dxsm, Pcg64Mcg};

macro_rules! gen_bytes {
    ($fnn:ident, $gen:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = $gen;
            let mut buf = [0u8; BYTES_LEN];
            b.iter(|| {
                for _ in 0..RAND_BENCH_N {
                    rng.fill_bytes(&mut buf);
                    black_box(buf);
                }
            });
            b.bytes = BYTES_LEN as u64 * RAND_BENCH_N;
        }
    };
}

gen_bytes!(gen_bytes_step, StepRng::new(0, 1));
gen_bytes!(gen_bytes_pcg32, Pcg32::from_os_rng());
gen_bytes!(gen_bytes_pcg64, Pcg64::from_os_rng());
gen_bytes!(gen_bytes_pcg64mcg, Pcg64Mcg::from_os_rng());
gen_bytes!(gen_bytes_pcg64dxsm, Pcg64Dxsm::from_os_rng());
gen_bytes!(gen_bytes_chacha8, ChaCha8Rng::from_os_rng());
gen_bytes!(gen_bytes_chacha12, ChaCha12Rng::from_os_rng());
gen_bytes!(gen_bytes_chacha20, ChaCha20Rng::from_os_rng());
gen_bytes!(gen_bytes_std, StdRng::from_os_rng());
gen_bytes!(gen_bytes_small, SmallRng::from_thread_rng());
gen_bytes!(gen_bytes_os, UnwrapErr(OsRng));
gen_bytes!(gen_bytes_thread, thread_rng());

macro_rules! gen_uint {
    ($fnn:ident, $ty:ty, $gen:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = $gen;
            b.iter(|| {
                let mut accum: $ty = 0;
                for _ in 0..RAND_BENCH_N {
                    accum = accum.wrapping_add(rng.random::<$ty>());
                }
                accum
            });
            b.bytes = size_of::<$ty>() as u64 * RAND_BENCH_N;
        }
    };
}

gen_uint!(gen_u32_step, u32, StepRng::new(0, 1));
gen_uint!(gen_u32_pcg32, u32, Pcg32::from_os_rng());
gen_uint!(gen_u32_pcg64, u32, Pcg64::from_os_rng());
gen_uint!(gen_u32_pcg64mcg, u32, Pcg64Mcg::from_os_rng());
gen_uint!(gen_u32_pcg64dxsm, u32, Pcg64Dxsm::from_os_rng());
gen_uint!(gen_u32_chacha8, u32, ChaCha8Rng::from_os_rng());
gen_uint!(gen_u32_chacha12, u32, ChaCha12Rng::from_os_rng());
gen_uint!(gen_u32_chacha20, u32, ChaCha20Rng::from_os_rng());
gen_uint!(gen_u32_std, u32, StdRng::from_os_rng());
gen_uint!(gen_u32_small, u32, SmallRng::from_thread_rng());
gen_uint!(gen_u32_os, u32, UnwrapErr(OsRng));
gen_uint!(gen_u32_thread, u32, thread_rng());

gen_uint!(gen_u64_step, u64, StepRng::new(0, 1));
gen_uint!(gen_u64_pcg32, u64, Pcg32::from_os_rng());
gen_uint!(gen_u64_pcg64, u64, Pcg64::from_os_rng());
gen_uint!(gen_u64_pcg64mcg, u64, Pcg64Mcg::from_os_rng());
gen_uint!(gen_u64_pcg64dxsm, u64, Pcg64Dxsm::from_os_rng());
gen_uint!(gen_u64_chacha8, u64, ChaCha8Rng::from_os_rng());
gen_uint!(gen_u64_chacha12, u64, ChaCha12Rng::from_os_rng());
gen_uint!(gen_u64_chacha20, u64, ChaCha20Rng::from_os_rng());
gen_uint!(gen_u64_std, u64, StdRng::from_os_rng());
gen_uint!(gen_u64_small, u64, SmallRng::from_thread_rng());
gen_uint!(gen_u64_os, u64, UnwrapErr(OsRng));
gen_uint!(gen_u64_thread, u64, thread_rng());

macro_rules! init_gen {
    ($fnn:ident, $gen:ident) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = Pcg32::from_os_rng();
            b.iter(|| {
                let r2 = $gen::from_rng(&mut rng);
                r2
            });
        }
    };
}

init_gen!(init_pcg32, Pcg32);
init_gen!(init_pcg64, Pcg64);
init_gen!(init_pcg64mcg, Pcg64Mcg);
init_gen!(init_pcg64dxsm, Pcg64Dxsm);
init_gen!(init_chacha, ChaCha20Rng);

const RESEEDING_BYTES_LEN: usize = 1024 * 1024;
const RESEEDING_BENCH_N: u64 = 16;

macro_rules! reseeding_bytes {
    ($fnn:ident, $thresh:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = ReseedingRng::new(ChaCha20Core::from_os_rng(), $thresh * 1024, OsRng);
            let mut buf = [0u8; RESEEDING_BYTES_LEN];
            b.iter(|| {
                for _ in 0..RESEEDING_BENCH_N {
                    rng.fill_bytes(&mut buf);
                    black_box(&buf);
                }
            });
            b.bytes = RESEEDING_BYTES_LEN as u64 * RESEEDING_BENCH_N;
        }
    };
}

reseeding_bytes!(reseeding_chacha20_4k, 4);
reseeding_bytes!(reseeding_chacha20_16k, 16);
reseeding_bytes!(reseeding_chacha20_32k, 32);
reseeding_bytes!(reseeding_chacha20_64k, 64);
reseeding_bytes!(reseeding_chacha20_256k, 256);
reseeding_bytes!(reseeding_chacha20_1M, 1024);
