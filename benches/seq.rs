#![feature(test)]

extern crate test;
extern crate rand;

use test::Bencher;

use rand::prelude::*;
use rand::seq::*;

#[bench]
fn misc_shuffle_100(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(thread_rng()).unwrap();
    let x : &mut [usize] = &mut [1; 100];
    b.iter(|| {
        rng.shuffle(x);
        x[0]
    })
}

#[bench]
fn misc_sample_iter_10_of_100(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(thread_rng()).unwrap();
    let x : &[usize] = &[1; 100];
    b.iter(|| {
        sample_iter(&mut rng, x, 10).unwrap_or_else(|e| e)
    })
}

#[bench]
fn misc_sample_slice_10_of_100(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(thread_rng()).unwrap();
    let x : &[usize] = &[1; 100];
    b.iter(|| {
        sample_slice(&mut rng, x, 10)
    })
}

#[bench]
fn misc_sample_slice_ref_10_of_100(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(thread_rng()).unwrap();
    let x : &[usize] = &[1; 100];
    b.iter(|| {
        sample_slice_ref(&mut rng, x, 10)
    })
}

macro_rules! sample_indices {
    ($name:ident, $amount:expr, $length:expr) => {
        #[bench]
        fn $name(b: &mut Bencher) {
            let mut rng = SmallRng::from_rng(thread_rng()).unwrap();
            b.iter(|| {
                sample_indices(&mut rng, $length, $amount)
            })
        }
    }
}

sample_indices!(misc_sample_indices_10_of_1k, 10, 1000);
sample_indices!(misc_sample_indices_50_of_1k, 50, 1000);
sample_indices!(misc_sample_indices_100_of_1k, 100, 1000);
