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

macro_rules! distr_range_int {
    ($fnn:ident, $ty:ty, $low:expr, $high:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = XorShiftRng::new().unwrap();
            let distr = Range::new($low, $high);

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

distr_range_int!(distr_range_i8, i8, 20i8, 100);
distr_range_int!(distr_range_i16, i16, -500i16, 2000);
distr_range_int!(distr_range_i32, i32, -200_000_000i32, 800_000_000);
distr_range_int!(distr_range_i64, i64, 3i64, 134217671);

macro_rules! distr_float {
    ($fnn:ident, $ty:ty, $distr:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = XorShiftRng::new().unwrap();
            let distr = $distr;

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

distr_float!(distr_uniform01_float32, f32, Uniform01);
distr_float!(distr_closed01_float32, f32, Closed01);
distr_float!(distr_open01_float32, f32, Open01);

distr_float!(distr_uniform01_float, f64, Uniform01);
distr_float!(distr_closed01_float, f64, Closed01);
distr_float!(distr_open01_float, f64, Open01);
distr_float!(distr_range_float, f64, Range::new(2.26f64, 2.319f64));
distr_float!(distr_exp, f64, Exp::new(2.71828 * 3.14159));
distr_float!(distr_normal, f64, Normal::new(-2.71828, 3.14159));
distr_float!(distr_log_normal, f64, LogNormal::new(-2.71828, 3.14159));
distr_float!(distr_gamma_large_shape, f64, Gamma::new(10., 1.0));
distr_float!(distr_gamma_small_shape, f64, Gamma::new(0.1, 1.0));
