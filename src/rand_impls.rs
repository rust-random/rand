// Copyright 2013-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The implementations of `Rand` for the built-in types.

macro_rules! float_impls {
    ($mod_name:ident, $ty:ty, $mantissa_bits:expr, $method_name:ident) => {
        mod $mod_name {
            use {Rand, Rng, Open01, Closed01};

            const SCALE: $ty = (1u64 << $mantissa_bits) as $ty;

            impl Rand for Open01<$ty> {
                #[inline]
                fn rand<R: Rng>(rng: &mut R) -> Open01<$ty> {
                    // add a small amount (specifically 2 bits below
                    // the precision of f64/f32 at 1.0), so that small
                    // numbers are larger than 0, but large numbers
                    // aren't pushed to/above 1.
                    Open01(rng.$method_name() + 0.25 / SCALE)
                }
            }
            impl Rand for Closed01<$ty> {
                #[inline]
                fn rand<R: Rng>(rng: &mut R) -> Closed01<$ty> {
                    // rescale so that 1.0 - epsilon becomes 1.0
                    // precisely.
                    Closed01(rng.$method_name() * SCALE / (SCALE - 1.0))
                }
            }
        }
    }
}
float_impls! { f64_rand_impls, f64, 53, next_f64 }
float_impls! { f32_rand_impls, f32, 24, next_f32 }

#[cfg(test)]
mod tests {
    use {Rng, thread_rng, Open01, Closed01};

    struct ConstantRng(u64);
    impl Rng for ConstantRng {
        fn next_u32(&mut self) -> u32 {
            let ConstantRng(v) = *self;
            v as u32
        }
        fn next_u64(&mut self) -> u64 {
            let ConstantRng(v) = *self;
            v
        }
    }

    #[test]
    fn floating_point_edge_cases() {
        // the test for exact equality is correct here.
        assert!(ConstantRng(0xffff_ffff).gen::<f32>() != 1.0);
        assert!(ConstantRng(0xffff_ffff_ffff_ffff).gen::<f64>() != 1.0);
    }

    #[test]
    fn rand_open() {
        // this is unlikely to catch an incorrect implementation that
        // generates exactly 0 or 1, but it keeps it sane.
        let mut rng = thread_rng();
        for _ in 0..1_000 {
            // strict inequalities
            let Open01(f) = rng.gen::<Open01<f64>>();
            assert!(0.0 < f && f < 1.0);

            let Open01(f) = rng.gen::<Open01<f32>>();
            assert!(0.0 < f && f < 1.0);
        }
    }

    #[test]
    fn rand_closed() {
        let mut rng = thread_rng();
        for _ in 0..1_000 {
            // strict inequalities
            let Closed01(f) = rng.gen::<Closed01<f64>>();
            assert!(0.0 <= f && f <= 1.0);

            let Closed01(f) = rng.gen::<Closed01<f32>>();
            assert!(0.0 <= f && f <= 1.0);
        }
    }
}
