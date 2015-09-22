#![feature(test)]

extern crate test;
extern crate rand;

mod distributions;

use test::Bencher;
use rand::{weak_rng, Rng};

pub const RAND_BENCH_N: u64 = 100;

#[bench]
fn rand_shuffle_100(b: &mut Bencher) {
    let mut rng = weak_rng();
    let x : &mut [usize] = &mut [1; 100];
    b.iter(|| {
        rng.shuffle(x)
    })
}

mod algorithms {
    use test::{black_box, Bencher};
    use std::mem::size_of;
    use rand::{OsRng, StdRng, weak_rng, XorShiftRng, XorShiftPlusRng, IsaacRng, Isaac64Rng, Rng, ChaChaRng};

    use super::*;

    macro_rules! impl_bench {
        ($result_ty: ty: $fn_name: ident, $hasher: ident) => (
            #[bench]
            fn $fn_name(b: &mut Bencher) {
                let mut rng: $hasher = OsRng::new().unwrap().gen();
                b.iter(|| {
                    for _ in 0..RAND_BENCH_N {
                        black_box(rng.gen::<$result_ty>());
                    }
                });
                b.bytes = size_of::<$result_ty>() as u64 * RAND_BENCH_N;
            }
        )
    }

    impl_bench!(u32: rand_xorshift_u32, XorShiftRng);
    impl_bench!(u64: rand_xorshift_u64, XorShiftRng);
    impl_bench!(u32: rand_rand_xorshiftplus_u32, XorShiftPlusRng);
    impl_bench!(u64: rand_xorshiftplus_u64, XorShiftPlusRng);
    impl_bench!(u32: rand_isaac_u32, IsaacRng);
    impl_bench!(u64: rand_isaac_u64, IsaacRng);
    impl_bench!(u32: rand_isaac64_u32, Isaac64Rng);
    impl_bench!(u64: rand_isaac64_u64, Isaac64Rng);
    impl_bench!(u32: rand_chacha_u32, ChaChaRng);
    impl_bench!(u64: rand_chacha_u64, ChaChaRng);

    #[bench]
    fn rand_std(b: &mut Bencher) {
        let mut rng = StdRng::new().unwrap();
        b.iter(|| {
            for _ in 0..RAND_BENCH_N {
                black_box(rng.gen::<usize>());
            }
        });
        b.bytes = size_of::<usize>() as u64 * RAND_BENCH_N;
    }

    #[bench]
    fn rand_weak(b: &mut Bencher) {
        let mut rng = weak_rng();
        b.iter(|| {
            for _ in 0..RAND_BENCH_N {
                black_box(rng.gen::<usize>());
            }
        });
        b.bytes = size_of::<usize>() as u64 * RAND_BENCH_N;
    }
}