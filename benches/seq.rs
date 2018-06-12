#![feature(test)]

extern crate test;
extern crate rand;

use test::Bencher;

use rand::prelude::*;
use rand::seq::*;

#[bench]
fn seq_shuffle_100(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(thread_rng()).unwrap();
    let x : &mut [usize] = &mut [1; 100];
    b.iter(|| {
        x.shuffle(&mut rng);
        x[0]
    })
}

#[bench]
fn seq_slice_sample_10_of_100(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(thread_rng()).unwrap();
    let x : &[usize] = &[1; 100];
    let mut buf = [0; 10];
    b.iter(|| {
        for (v, slot) in x.sample(&mut rng, buf.len()).zip(buf.iter_mut()) {
            *slot = *v;
        }
        buf
    })
}

#[bench]
fn seq_iter_choose_from_100(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(thread_rng()).unwrap();
    let x : &[usize] = &[1; 100];
    b.iter(|| {
        x.iter().cloned().choose(&mut rng)
    })
}

#[bench]
fn seq_iter_sample_10_of_100(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(thread_rng()).unwrap();
    let x : &[usize] = &[1; 100];
    b.iter(|| {
        x.iter().cloned().sample(&mut rng, 10) /*.unwrap_or_else(|e| e)*/
    })
}

#[bench]
fn seq_iter_sample_fill_10_of_100(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(thread_rng()).unwrap();
    let x : &[usize] = &[1; 100];
    let mut buf = [0; 10];
    b.iter(|| {
        x.iter().cloned().sample_fill(&mut rng, &mut buf)
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

sample_indices!(seq_sample_indices_10_of_1k, 10, 1000);
sample_indices!(seq_sample_indices_50_of_1k, 50, 1000);
sample_indices!(seq_sample_indices_100_of_1k, 100, 1000);
