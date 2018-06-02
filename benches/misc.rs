#![feature(test)]

extern crate test;
extern crate rand;

const RAND_BENCH_N: u64 = 1000;

use test::Bencher;

use rand::prelude::*;
use rand::seq::*;

#[bench]
fn misc_gen_bool_const(b: &mut Bencher) {
    let mut rng = StdRng::from_rng(&mut thread_rng()).unwrap();
    b.iter(|| {
        let mut accum = true;
        for _ in 0..::RAND_BENCH_N {
            accum ^= rng.gen_bool(0.18);
        }
        accum
    })
}

#[bench]
fn misc_gen_bool_var(b: &mut Bencher) {
    let mut rng = StdRng::from_rng(&mut thread_rng()).unwrap();
    b.iter(|| {
        let mut accum = true;
        let mut p = 0.18;
        for _ in 0..::RAND_BENCH_N {
            accum ^= rng.gen_bool(p);
            p += 0.0001;
        }
        accum
    })
}

#[bench]
fn misc_bernoulli_const(b: &mut Bencher) {
    let mut rng = StdRng::from_rng(&mut thread_rng()).unwrap();
    let d = rand::distributions::Bernoulli::new(0.18);
    b.iter(|| {
        // Can be evaluated at compile time.
        let mut accum = true;
        for _ in 0..::RAND_BENCH_N {
            accum ^= rng.sample(d);
        }
        accum
    })
}

#[bench]
fn misc_bernoulli_var(b: &mut Bencher) {
    let mut rng = StdRng::from_rng(&mut thread_rng()).unwrap();
    b.iter(|| {
        let mut accum = true;
        let mut p = 0.18;
        for _ in 0..::RAND_BENCH_N {
            let d = rand::distributions::Bernoulli::new(p);
            accum ^= rng.sample(d);
            p += 0.0001;
        }
        accum
    })
}

macro_rules! sample_binomial {
    ($name:ident, $n:expr, $p:expr) => {
        #[bench]
        fn $name(b: &mut Bencher) {
            let mut rng = SmallRng::from_rng(&mut thread_rng()).unwrap();
            let (n, p) = ($n, $p);
            b.iter(|| {
                let d = rand::distributions::Binomial::new(n, p);
                rng.sample(d)
            })
        }
    }
}

sample_binomial!(misc_binomial_1, 1, 0.9);
sample_binomial!(misc_binomial_10, 10, 0.9);
sample_binomial!(misc_binomial_100, 100, 0.99);
sample_binomial!(misc_binomial_1000, 1000, 0.01);
sample_binomial!(misc_binomial_1e12, 1000_000_000_000, 0.2);

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

#[bench]
fn gen_1k_iter_repeat(b: &mut Bencher) {
    use std::iter;
    let mut rng = SmallRng::from_rng(&mut thread_rng()).unwrap();
    b.iter(|| {
        let v: Vec<u64> = iter::repeat(()).map(|()| rng.gen()).take(128).collect();
        v
    });
    b.bytes = 1024;
}

#[bench]
#[allow(deprecated)]
fn gen_1k_gen_iter(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(&mut thread_rng()).unwrap();
    b.iter(|| {
        let v: Vec<u64> = rng.gen_iter().take(128).collect();
        v
    });
    b.bytes = 1024;
}

#[bench]
fn gen_1k_sample_iter(b: &mut Bencher) {
    use rand::distributions::{Distribution, Standard};
    let mut rng = SmallRng::from_rng(&mut thread_rng()).unwrap();
    b.iter(|| {
        let v: Vec<u64> = Standard.sample_iter(&mut rng).take(128).collect();
        v
    });
    b.bytes = 1024;
}

#[bench]
fn gen_1k_gen_array(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(&mut thread_rng()).unwrap();
    b.iter(|| {
        // max supported array length is 32!
        let v: [[u64; 32]; 4] = rng.gen();
        v
    });
    b.bytes = 1024;
}

#[bench]
fn gen_1k_fill(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(&mut thread_rng()).unwrap();
    let mut buf = [0u64; 128];
    b.iter(|| {
        rng.fill(&mut buf[..]);
        buf
    });
    b.bytes = 1024;
}
