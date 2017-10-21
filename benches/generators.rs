#![feature(test)]

extern crate test;
extern crate rand;

const RAND_BENCH_N: u64 = 1000;
const BYTES_LEN: usize = 1024;

use std::mem::size_of;
use test::{black_box, Bencher};

use rand::{Rng, NewSeeded, SeedFromRng, StdRng, OsRng, Rand, Default};
use rand::prng::{XorShiftRng, IsaacRng, Isaac64Rng, ChaChaRng};

macro_rules! gen_bytes {
    ($fnn:ident, $gen:ident) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = $gen::new().unwrap();
            let mut buf = [0u8; BYTES_LEN];
            b.iter(|| {
                for _ in 0..RAND_BENCH_N {
                    rng.try_fill(&mut buf).unwrap();
                    black_box(buf);
                }
            });
            b.bytes = BYTES_LEN as u64 * RAND_BENCH_N;
        }
    }
}

gen_bytes!(gen_bytes_xorshift, XorShiftRng);
gen_bytes!(gen_bytes_isaac, IsaacRng);
gen_bytes!(gen_bytes_isaac64, Isaac64Rng);
gen_bytes!(gen_bytes_chacha, ChaChaRng);
gen_bytes!(gen_bytes_std, StdRng);
gen_bytes!(gen_bytes_os, OsRng);


macro_rules! gen_usize {
    ($fnn:ident, $gen:ident) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = $gen::new().unwrap();
            b.iter(|| {
                for _ in 0..RAND_BENCH_N {
                    black_box(usize::rand(&mut rng, Default));
                }
            });
            b.bytes = size_of::<usize>() as u64 * RAND_BENCH_N;
        }
    }
}

gen_usize!(gen_usize_xorshift, XorShiftRng);
gen_usize!(gen_usize_isaac, IsaacRng);
gen_usize!(gen_usize_isaac64, Isaac64Rng);
gen_usize!(gen_usize_chacha, ChaChaRng);
gen_usize!(gen_usize_std, StdRng);
gen_usize!(gen_usize_os, OsRng);

macro_rules! init_gen {
    ($fnn:ident, $gen:ident) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = XorShiftRng::new().unwrap();
            b.iter(|| {
                for _ in 0..RAND_BENCH_N {
                    black_box($gen::from_rng(&mut rng).unwrap());
                }
            });
        }
    }
}

init_gen!(init_xorshift, XorShiftRng);
init_gen!(init_isaac, IsaacRng);
init_gen!(init_isaac64, Isaac64Rng);
init_gen!(init_chacha, ChaChaRng);
init_gen!(init_std, StdRng);
