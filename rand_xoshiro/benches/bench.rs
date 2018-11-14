#![allow(unknown_lints)]

#[macro_use]
extern crate bencher;
extern crate rand_xoshiro;
extern crate rand_core;

use std::mem::size_of;
use bencher::{black_box, Bencher};
use rand_xoshiro::Xoshiro128StarStar;
use rand_core::{SeedableRng, RngCore};

macro_rules! make_bench_u32 {
    ($name:ident, $rng:path) => {
        fn $name(b: &mut Bencher) {
            type Rng = $rng;
            let mut rng = Rng::from_seed([1, 0, 0, 0, 2, 0, 0, 0,
                                          3, 0, 0, 0, 4, 0, 0, 0]);
            b.iter(|| {
                for _ in 0..10 {
                    black_box(rng.next_u32());
                }
            });
            b.bytes = size_of::<u32>() as u64;
        }
    }
}

make_bench_u32!(rand_u32_xoshiro, Xoshiro128StarStar);

benchmark_group!(benches, rand_u32_xoshiro);
benchmark_main!(benches);
