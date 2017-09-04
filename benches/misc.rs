#![feature(test)]

extern crate test;
extern crate rand;

const RAND_BENCH_N: u64 = 1000;

use std::mem::size_of;
use test::{black_box, Bencher};
use rand::StdRng;
use rand::prng::XorShiftRng;
use rand::sequences::{sample, Shuffle};
use rand::distributions::{Rand, Uniform, Uniform01, Closed01, Open01};

#[bench]
fn misc_shuffle_100(b: &mut Bencher) {
    let mut rng = XorShiftRng::new().unwrap();
    let x : &mut [usize] = &mut [1; 100];
    b.iter(|| {
        x.shuffle(&mut rng);
        black_box(&x);
    })
}

#[bench]
fn misc_sample_10_of_100(b: &mut Bencher) {
    let mut rng = XorShiftRng::new().unwrap();
    let x : &[usize] = &[1; 100];
    b.iter(|| {
        black_box(sample(&mut rng, x, 10));
    })
}
