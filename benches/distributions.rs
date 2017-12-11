#![feature(test)]
#![cfg_attr(feature = "i128_support", feature(i128_type, i128))]

extern crate test;
extern crate rand;

const RAND_BENCH_N: u64 = 1000;

use std::mem::size_of;
use test::{black_box, Bencher};

use rand::NewSeeded;
use rand::prng::XorShiftRng;
use rand::distributions::*;

macro_rules! distr {
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

// range
distr!(distr_range_i8, i8, Range::new(20i8, 100));
distr!(distr_range_i16, i16, Range::new(-500i16, 2000));
distr!(distr_range_i32, i32, Range::new(-200_000_000i32, 800_000_000));
distr!(distr_range_i64, i64, Range::new(3i64, 12345678901234));
#[cfg(feature = "i128_support")]
distr!(distr_range_i128, i128, Range::new(-12345678901234i128, 12345678901234567890));

distr!(distr_range_float32, f32, Range::new(2.26f32, 2.319));
distr!(distr_range_float, f64, Range::new(2.26f64, 2.319));

// uniform
distr!(distr_uniform_i8, i8, Uniform);
distr!(distr_uniform_i16, i16, Uniform);
distr!(distr_uniform_i32, i32, Uniform);
distr!(distr_uniform_i64, i64, Uniform);
#[cfg(feature = "i128_support")]
distr!(distr_uniform_i128, i128, Uniform);

distr!(distr_uniform_bool, bool, Uniform);
distr!(distr_uniform_ascii_char, char, AsciiWordChar);

distr!(distr_uniform01_float32, f32, Uniform01);
distr!(distr_closed01_float32, f32, Closed01);
distr!(distr_open01_float32, f32, Open01);

distr!(distr_uniform01_float, f64, Uniform01);
distr!(distr_closed01_float, f64, Closed01);
distr!(distr_open01_float, f64, Open01);

// distributions
distr!(distr_exp, f64, Exp::new(2.71828 * 3.14159));
distr!(distr_normal, f64, Normal::new(-2.71828, 3.14159));
distr!(distr_log_normal, f64, LogNormal::new(-2.71828, 3.14159));
distr!(distr_gamma_large_shape, f64, Gamma::new(10., 1.0));
distr!(distr_gamma_small_shape, f64, Gamma::new(0.1, 1.0));


// construct and sample from a range
macro_rules! gen_range_int {
    ($fnn:ident, $ty:ty, $low:expr, $high:expr) => {
        #[bench]
        fn $fnn(b: &mut Bencher) {
            let mut rng = XorShiftRng::new().unwrap();

            b.iter(|| {
                for _ in 0..::RAND_BENCH_N {
                    let x: $ty = Range::new($low, $high).sample(&mut rng);
                    black_box(x);
                }
            });
            b.bytes = size_of::<$ty>() as u64 * ::RAND_BENCH_N;
        }
    }
}

gen_range_int!(gen_range_i8, i8, 20i8, 100);
gen_range_int!(gen_range_i16, i16, -500i16, 2000);
gen_range_int!(gen_range_i32, i32, -200_000_000i32, 800_000_000);
gen_range_int!(gen_range_i64, i64, 3i64, 12345678901234);
#[cfg(feature = "i128_support")]
gen_range_int!(gen_range_i128, i128, -12345678901234i128, 12345678901234567890);
