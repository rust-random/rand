#![feature(test)]

extern crate test;
extern crate rand;

const RAND_BENCH_N: u64 = 1000;

use std::mem::size_of;
use test::{black_box, Bencher};

use rand::{StdRng, OsRng, Rand, Default};
use rand::prng::{XorShiftRng, IsaacRng, Isaac64Rng, ChaChaRng};

#[bench]
fn gen_usize_xorshift(b: &mut Bencher) {
    let mut rng = XorShiftRng::new_from_rng(&mut OsRng::new().unwrap());
    b.iter(|| {
        for _ in 0..RAND_BENCH_N {
            black_box(usize::rand(&mut rng, Default));
        }
    });
    b.bytes = size_of::<usize>() as u64 * RAND_BENCH_N;
}

#[bench]
fn gen_usize_isaac(b: &mut Bencher) {
    let mut rng = IsaacRng::new_from_rng(&mut OsRng::new().unwrap());
    b.iter(|| {
        for _ in 0..RAND_BENCH_N {
            black_box(usize::rand(&mut rng, Default));
        }
    });
    b.bytes = size_of::<usize>() as u64 * RAND_BENCH_N;
}

#[bench]
fn gen_usize_isaac64(b: &mut Bencher) {
    let mut rng = Isaac64Rng::new_from_rng(&mut OsRng::new().unwrap());
    b.iter(|| {
        for _ in 0..RAND_BENCH_N {
            black_box(usize::rand(&mut rng, Default));
        }
    });
    b.bytes = size_of::<usize>() as u64 * RAND_BENCH_N;
}

#[bench]
fn gen_usize_chacha(b: &mut Bencher) {
    let mut rng = ChaChaRng::new_from_rng(&mut OsRng::new().unwrap());
    b.iter(|| {
        for _ in 0..RAND_BENCH_N {
            black_box(usize::rand(&mut rng, Default));
        }
    });
    b.bytes = size_of::<usize>() as u64 * RAND_BENCH_N;
}

#[bench]
fn gen_usize_std(b: &mut Bencher) {
    let mut rng = StdRng::new().unwrap();
    b.iter(|| {
        for _ in 0..RAND_BENCH_N {
            black_box(usize::rand(&mut rng, Default));
        }
    });
    b.bytes = size_of::<usize>() as u64 * RAND_BENCH_N;
}

#[bench]
fn gen_usize_os(b: &mut Bencher) {
    let mut rng = OsRng::new().unwrap();
    b.iter(|| {
        for _ in 0..RAND_BENCH_N {
            black_box(usize::rand(&mut rng, Default));
        }
    });
    b.bytes = size_of::<usize>() as u64 * RAND_BENCH_N;
}
