#![feature(test)]

extern crate test;
extern crate rand;

const RAND_BENCH_N: u64 = 1000;

use std::mem::size_of;
use test::{black_box, Bencher};
use rand::{StdRng, weak_rng};
use rand::sequences::{sample, Shuffle};
use rand::distributions::{Rand, Uniform, Uniform01};

#[bench]
fn misc_baseline_32(b: &mut Bencher) {
    let mut rng = StdRng::new().unwrap();
    b.iter(|| {
        for _ in 0..RAND_BENCH_N {
            black_box(u32::rand(&mut rng, Uniform));
        }
    });
    b.bytes = size_of::<u32>() as u64 * RAND_BENCH_N;
}

#[bench]
fn misc_baseline_64(b: &mut Bencher) {
    let mut rng = StdRng::new().unwrap();
    b.iter(|| {
        for _ in 0..RAND_BENCH_N {
            black_box(u64::rand(&mut rng, Uniform));
        }
    });
    b.bytes = size_of::<u64>() as u64 * RAND_BENCH_N;
}

#[bench]
fn misc_convert_f32(b: &mut Bencher) {
    let mut rng = StdRng::new().unwrap();
    b.iter(|| {
        for _ in 0..RAND_BENCH_N {
            black_box(f32::rand(&mut rng, Uniform01));
        }
    });
    b.bytes = size_of::<f32>() as u64 * RAND_BENCH_N;
}

#[bench]
fn misc_convert_f64(b: &mut Bencher) {
    let mut rng = StdRng::new().unwrap();
    b.iter(|| {
        for _ in 0..RAND_BENCH_N {
            black_box(f64::rand(&mut rng, Uniform01));
        }
    });
    b.bytes = size_of::<f64>() as u64 * RAND_BENCH_N;
}

#[bench]
fn misc_shuffle_100(b: &mut Bencher) {
    let mut rng = weak_rng();
    let x : &mut [usize] = &mut [1; 100];
    b.iter(|| {
        x.shuffle(&mut rng);
    })
}

#[bench]
fn misc_sample_10_of_100(b: &mut Bencher) {
    let mut rng = weak_rng();
    let x : &[usize] = &[1; 100];
    b.iter(|| {
        sample(&mut rng, x, 10);
    })
}
