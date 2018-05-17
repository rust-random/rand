#![feature(test)]

extern crate test;
extern crate rand;

const RAND_BENCH_N: u64 = 1000;
const BYTES_LEN: usize = 1024;

use std::mem::size_of;
use test::{black_box, Bencher};

use rand::prelude::*;
use rand::prng::{XorShiftRng, Hc128Rng, IsaacRng, Isaac64Rng, ChaChaRng};
use rand::prng::hc128::Hc128Core;
use rand::rngs::adapter::ReseedingRng;
use rand::rngs::{OsRng, JitterRng, EntropyRng};

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
    }
}

gen_bytes!(gen_bytes_xorshift, XorShiftRng::from_entropy());
gen_bytes!(gen_bytes_chacha20, ChaChaRng::from_entropy());
gen_bytes!(gen_bytes_hc128, Hc128Rng::from_entropy());
gen_bytes!(gen_bytes_isaac, IsaacRng::from_entropy());
gen_bytes!(gen_bytes_isaac64, Isaac64Rng::from_entropy());
gen_bytes!(gen_bytes_std, StdRng::from_entropy());
gen_bytes!(gen_bytes_small, SmallRng::from_entropy());
gen_bytes!(gen_bytes_os, OsRng::new().unwrap());

macro_rules! gen_uint {
    ($fnn:ident, $ty:ty, $gen:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = $gen;
            b.iter(|| {
                let mut accum: $ty = 0;
                for _ in 0..RAND_BENCH_N {
                    accum = accum.wrapping_add(rng.gen::<$ty>());
                }
                accum
            });
            b.bytes = size_of::<$ty>() as u64 * RAND_BENCH_N;
        }
    }
}

gen_uint!(gen_u32_xorshift, u32, XorShiftRng::from_entropy());
gen_uint!(gen_u32_chacha20, u32, ChaChaRng::from_entropy());
gen_uint!(gen_u32_hc128, u32, Hc128Rng::from_entropy());
gen_uint!(gen_u32_isaac, u32, IsaacRng::from_entropy());
gen_uint!(gen_u32_isaac64, u32, Isaac64Rng::from_entropy());
gen_uint!(gen_u32_std, u32, StdRng::from_entropy());
gen_uint!(gen_u32_small, u32, SmallRng::from_entropy());
gen_uint!(gen_u32_os, u32, OsRng::new().unwrap());

gen_uint!(gen_u64_xorshift, u64, XorShiftRng::from_entropy());
gen_uint!(gen_u64_chacha20, u64, ChaChaRng::from_entropy());
gen_uint!(gen_u64_hc128, u64, Hc128Rng::from_entropy());
gen_uint!(gen_u64_isaac, u64, IsaacRng::from_entropy());
gen_uint!(gen_u64_isaac64, u64, Isaac64Rng::from_entropy());
gen_uint!(gen_u64_std, u64, StdRng::from_entropy());
gen_uint!(gen_u64_small, u64, SmallRng::from_entropy());
gen_uint!(gen_u64_os, u64, OsRng::new().unwrap());

// Do not test JitterRng like the others by running it RAND_BENCH_N times per,
// measurement, because it is way too slow. Only run it once.
#[bench]
fn gen_u64_jitter(b: &mut Bencher) {
    let mut rng = JitterRng::new().unwrap();
    b.iter(|| {
        rng.gen::<u64>()
    });
    b.bytes = size_of::<u64>() as u64;
}

macro_rules! init_gen {
    ($fnn:ident, $gen:ident) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = XorShiftRng::from_entropy();
            b.iter(|| {
                let r2 = $gen::from_rng(&mut rng).unwrap();
                r2
            });
        }
    }
}

init_gen!(init_xorshift, XorShiftRng);
init_gen!(init_hc128, Hc128Rng);
init_gen!(init_isaac, IsaacRng);
init_gen!(init_isaac64, Isaac64Rng);
init_gen!(init_chacha, ChaChaRng);

#[bench]
fn init_jitter(b: &mut Bencher) {
    b.iter(|| {
        JitterRng::new().unwrap()
    });
}


const RESEEDING_THRESHOLD: u64 = 1024*1024*1024; // something high enough to get
                                                 // deterministic measurements

#[bench]
fn reseeding_hc128_bytes(b: &mut Bencher) {
    let mut rng = ReseedingRng::new(Hc128Core::from_entropy(),
                                    RESEEDING_THRESHOLD,
                                    EntropyRng::new());
    let mut buf = [0u8; BYTES_LEN];
    b.iter(|| {
        for _ in 0..RAND_BENCH_N {
            rng.fill_bytes(&mut buf);
            black_box(buf);
        }
    });
    b.bytes = BYTES_LEN as u64 * RAND_BENCH_N;
}

macro_rules! reseeding_uint {
    ($fnn:ident, $ty:ty) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = ReseedingRng::new(Hc128Core::from_entropy(),
                                            RESEEDING_THRESHOLD,
                                            EntropyRng::new());
            b.iter(|| {
                let mut accum: $ty = 0;
                for _ in 0..RAND_BENCH_N {
                    accum = accum.wrapping_add(rng.gen::<$ty>());
                }
                accum
            });
            b.bytes = size_of::<$ty>() as u64 * RAND_BENCH_N;
        }
    }
}

reseeding_uint!(reseeding_hc128_u32, u32);
reseeding_uint!(reseeding_hc128_u64, u64);


macro_rules! threadrng_uint {
    ($fnn:ident, $ty:ty) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = thread_rng();
            b.iter(|| {
                let mut accum: $ty = 0;
                for _ in 0..RAND_BENCH_N {
                    accum = accum.wrapping_add(rng.gen::<$ty>());
                }
                accum
            });
            b.bytes = size_of::<$ty>() as u64 * RAND_BENCH_N;
        }
    }
}

threadrng_uint!(thread_rng_u32, u32);
threadrng_uint!(thread_rng_u64, u64);
