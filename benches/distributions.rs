#![feature(test)]

extern crate test;
extern crate rand;

const RAND_BENCH_N: u64 = 1000;

use std::mem::size_of;
use test::{black_box, Bencher};

use rand::{Default, Rand, NewSeeded};
use rand::prng::XorShiftRng;
use rand::distributions::*;


#[bench]
fn distr_baseline(b: &mut Bencher) {
    let mut rng = XorShiftRng::new().unwrap();

    b.iter(|| {
        for _ in 0..::RAND_BENCH_N {
            black_box(u64::rand(&mut rng, Default));
        }
    });
    b.bytes = size_of::<u64>() as u64 * ::RAND_BENCH_N;
}

#[bench]
fn distr_range_int(b: &mut Bencher) {
    let mut rng = XorShiftRng::new().unwrap();
    let distr = Range::new(3i64, 134217671i64);

    b.iter(|| {
        for _ in 0..::RAND_BENCH_N {
            black_box(distr.sample(&mut rng));
        }
    });
    b.bytes = size_of::<i64>() as u64 * ::RAND_BENCH_N;
}

macro_rules! distr_range2_int {
    ($fnn:ident, $ty:ty, $low:expr, $high:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = XorShiftRng::new().unwrap();
            let distr = range2::Range::new($low, $high);

            b.iter(|| {
                for _ in 0..::RAND_BENCH_N {
                    let x: $ty = distr.sample(&mut rng);
                    black_box(x);
                }
            });
            b.bytes = size_of::<$ty>() as u64 * ::RAND_BENCH_N;
        }
    }
}

distr_range2_int!(distr_range2_i8, i8, 20i8, 100);
distr_range2_int!(distr_range2_i16, i16, -500i16, 2000);
distr_range2_int!(distr_range2_i32, i32, -200_000_000i32, 800_000_000);
distr_range2_int!(distr_range2_i64, i64, 3i64, 134217671);

macro_rules! distr_float {
    ($fnn:ident, $distr:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = XorShiftRng::new().unwrap();
            let distr = $distr;

            b.iter(|| {
                for _ in 0..::RAND_BENCH_N {
                    let x: f64 = distr.sample(&mut rng);
                    black_box(x);
                }
            });
            b.bytes = size_of::<f64>() as u64 * ::RAND_BENCH_N;
        }
    }
}

distr_float!(distr_uniform01_float, Uniform01);
distr_float!(distr_closed01_float, Closed01);
distr_float!(distr_open01_float, Open01);
distr_float!(distr_range_float, Range::new(2.26f64, 2.319f64));
distr_float!(distr_range2_float, range2::Range::new(2.26f64, 2.319f64));
distr_float!(distr_exp, Exp::new(2.71828 * 3.14159));
distr_float!(distr_normal, Normal::new(-2.71828, 3.14159));
distr_float!(distr_log_normal, LogNormal::new(-2.71828, 3.14159));
distr_float!(distr_gamma_large_shape, Gamma::new(10., 1.0));
distr_float!(distr_gamma_small_shape, Gamma::new(0.1, 1.0));
