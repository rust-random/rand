#![feature(test)]

extern crate test;
extern crate rand;

const RAND_BENCH_N: u64 = 1000;

mod distributions;

use std::mem::size_of;
use test::{black_box, Bencher};
use rand::{StdRng, OsRng, weak_rng};
use rand::prng::{XorShiftRng, IsaacRng, Isaac64Rng};
use rand::{sample, Shuffle};
use rand::distributions::{Rand, Uniform, Uniform01};

#[bench]
fn rand_xorshift(b: &mut Bencher) {
    let mut rng = XorShiftRng::new_from_rng(&mut OsRng::new().unwrap());
    b.iter(|| {
        for _ in 0..RAND_BENCH_N {
            black_box(usize::rand(&mut rng, Uniform));
        }
    });
    b.bytes = size_of::<usize>() as u64 * RAND_BENCH_N;
}

#[bench]
fn rand_isaac(b: &mut Bencher) {
    let mut rng = IsaacRng::new_from_rng(&mut OsRng::new().unwrap());
    b.iter(|| {
        for _ in 0..RAND_BENCH_N {
            black_box(usize::rand(&mut rng, Uniform));
        }
    });
    b.bytes = size_of::<usize>() as u64 * RAND_BENCH_N;
}

#[bench]
fn rand_isaac64(b: &mut Bencher) {
    let mut rng = Isaac64Rng::new_from_rng(&mut OsRng::new().unwrap());
    b.iter(|| {
        for _ in 0..RAND_BENCH_N {
            black_box(usize::rand(&mut rng, Uniform));
        }
    });
    b.bytes = size_of::<usize>() as u64 * RAND_BENCH_N;
}

#[bench]
fn rand_std(b: &mut Bencher) {
    let mut rng = StdRng::new().unwrap();
    b.iter(|| {
        for _ in 0..RAND_BENCH_N {
            black_box(usize::rand(&mut rng, Uniform));
        }
    });
    b.bytes = size_of::<usize>() as u64 * RAND_BENCH_N;
}

#[bench]
fn rand_f32(b: &mut Bencher) {
    let mut rng = StdRng::new().unwrap();
    b.iter(|| {
        for _ in 0..RAND_BENCH_N {
            black_box(f32::rand(&mut rng, Uniform01));
        }
    });
    b.bytes = size_of::<f32>() as u64 * RAND_BENCH_N;
}

#[bench]
fn rand_f64(b: &mut Bencher) {
    let mut rng = StdRng::new().unwrap();
    b.iter(|| {
        for _ in 0..RAND_BENCH_N {
            black_box(f64::rand(&mut rng, Uniform01));
        }
    });
    b.bytes = size_of::<f64>() as u64 * RAND_BENCH_N;
}

#[bench]
fn rand_shuffle_100(b: &mut Bencher) {
    let mut rng = weak_rng();
    let x : &mut [usize] = &mut [1; 100];
    b.iter(|| {
        x.shuffle(&mut rng);
    })
}

#[bench]
fn rand_sample_10_of_100(b: &mut Bencher) {
    let mut rng = weak_rng();
    let x : &[usize] = &[1; 100];
    b.iter(|| {
        sample(&mut rng, x, 10);
    })
}
