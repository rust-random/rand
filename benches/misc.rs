#![feature(test)]

extern crate test;
extern crate rand;

use test::{black_box, Bencher};

use rand::Rng;
use rand::{sample, weak_rng};

#[bench]
fn misc_shuffle_100(b: &mut Bencher) {
    let mut rng = weak_rng();
    let x : &mut [usize] = &mut [1; 100];
    b.iter(|| {
        rng.shuffle(x);
        black_box(&x);
    })
}

#[bench]
fn misc_sample_10_of_100(b: &mut Bencher) {
    let mut rng = weak_rng();
    let x : &[usize] = &[1; 100];
    b.iter(|| {
        black_box(sample(&mut rng, x, 10));
    })
}
