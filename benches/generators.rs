#![feature(test)]

extern crate test;
extern crate rand;

const RAND_BENCH_N: u64 = 1000;
const BYTES_LEN: usize = 1024;

use std::mem::size_of;
use test::{black_box, Bencher};

use rand::{RngCore, Rng, SeedableRng, NewRng, StdRng, OsRng, JitterRng, EntropyRng};
use rand::{XorShiftRng, Hc128Rng, IsaacRng, Isaac64Rng, ChaChaRng};
use rand::reseeding::ReseedingRng;

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

gen_bytes!(gen_bytes_xorshift, XorShiftRng::new());
gen_bytes!(gen_bytes_hc128, Hc128Rng::new());
gen_bytes!(gen_bytes_isaac, IsaacRng::new());
gen_bytes!(gen_bytes_isaac64, Isaac64Rng::new());
gen_bytes!(gen_bytes_std, StdRng::new());
gen_bytes!(gen_bytes_os, OsRng::new().unwrap());

macro_rules! gen_uint {
    ($fnn:ident, $ty:ty, $gen:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = $gen;
            b.iter(|| {
                for _ in 0..RAND_BENCH_N {
                    black_box(rng.gen::<$ty>());
                }
            });
            b.bytes = size_of::<$ty>() as u64 * RAND_BENCH_N;
        }
    }
}

gen_uint!(gen_u32_xorshift, u32, XorShiftRng::new());
gen_uint!(gen_u32_hc128, u32, Hc128Rng::new());
gen_uint!(gen_u32_isaac, u32, IsaacRng::new());
gen_uint!(gen_u32_isaac64, u32, Isaac64Rng::new());
gen_uint!(gen_u32_std, u32, StdRng::new());
gen_uint!(gen_u32_os, u32, OsRng::new().unwrap());

gen_uint!(gen_u64_xorshift, u64, XorShiftRng::new());
gen_uint!(gen_u64_hc128, u64, Hc128Rng::new());
gen_uint!(gen_u64_isaac, u64, IsaacRng::new());
gen_uint!(gen_u64_isaac64, u64, Isaac64Rng::new());
gen_uint!(gen_u64_std, u64, StdRng::new());
gen_uint!(gen_u64_os, u64, OsRng::new().unwrap());

// Do not test JitterRng like the others by running it RAND_BENCH_N times per,
// measurement, because it is way too slow. Only run it once.
#[bench]
fn gen_u64_jitter(b: &mut Bencher) {
    let mut rng = JitterRng::new().unwrap();
    b.iter(|| {
        black_box(rng.gen::<u64>());
    });
    b.bytes = size_of::<u64>() as u64;
}

macro_rules! init_gen {
    ($fnn:ident, $gen:ident) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = XorShiftRng::new();
            b.iter(|| {
                let r2 = $gen::from_rng(&mut rng).unwrap();
                black_box(r2);
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
        black_box(JitterRng::new().unwrap());
    });
}

macro_rules! chacha_rounds {
    ($fn1:ident, $fn2:ident, $fn3:ident, $rounds:expr) => {
        #[bench]
        fn $fn1(b: &mut Bencher) {
            let mut rng = ChaChaRng::new();
            rng.set_rounds($rounds);
            let mut buf = [0u8; BYTES_LEN];
            b.iter(|| {
                for _ in 0..RAND_BENCH_N {
                    rng.fill_bytes(&mut buf);
                    black_box(buf);
                }
            });
            b.bytes = BYTES_LEN as u64 * RAND_BENCH_N;
        }

        #[bench]
        fn $fn2(b: &mut Bencher) {
            let mut rng = ChaChaRng::new();
            rng.set_rounds($rounds);
            b.iter(|| {
                for _ in 0..RAND_BENCH_N {
                    black_box(rng.gen::<u32>());
                }
            });
            b.bytes = size_of::<u32>() as u64 * RAND_BENCH_N;
        }

        #[bench]
        fn $fn3(b: &mut Bencher) {
            let mut rng = ChaChaRng::new();
            rng.set_rounds($rounds);
            b.iter(|| {
                for _ in 0..RAND_BENCH_N {
                    black_box(rng.gen::<u64>());
                }
            });
            b.bytes = size_of::<u64>() as u64 * RAND_BENCH_N;
        }
    }
}

chacha_rounds!(gen_bytes_chacha8, gen_u32_chacha8, gen_u64_chacha8, 8);
chacha_rounds!(gen_bytes_chacha12, gen_u32_chacha12, gen_u64_chacha12, 12);
chacha_rounds!(gen_bytes_chacha20, gen_u32_chacha20, gen_u64_chacha20, 20);


#[bench]
fn reseeding_hc128_bytes(b: &mut Bencher) {
    let mut rng = ReseedingRng::new(Hc128Rng::new(),
                                    128*1024*1024,
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
            let mut rng = ReseedingRng::new(Hc128Rng::new(),
                                            128*1024*1024,
                                            EntropyRng::new());
            b.iter(|| {
                for _ in 0..RAND_BENCH_N {
                    black_box(rng.gen::<$ty>());
                }
            });
            b.bytes = size_of::<$ty>() as u64 * RAND_BENCH_N;
        }
    }
}

reseeding_uint!(reseeding_hc128_u32, u32);
reseeding_uint!(reseeding_hc128_u64, u64);
