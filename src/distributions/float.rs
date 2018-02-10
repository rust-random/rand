// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Basic floating-point number distributions


/// A distribution to sample floating point numbers uniformly in the open
/// interval `(0, 1)` (not including either endpoint).
///
/// See also: [`Closed01`] for the closed `[0, 1]`; [`Uniform`] for the
/// half-open `[0, 1)`.
///
/// # Example
/// ```rust
/// use rand::{weak_rng, Rng};
/// use rand::distributions::Open01;
///
/// let val: f32 = weak_rng().sample(Open01);
/// println!("f32 from (0,1): {}", val);
/// ```
///
/// [`Uniform`]: struct.Uniform.html
/// [`Closed01`]: struct.Closed01.html
#[derive(Clone, Copy, Debug)]
pub struct Open01;

/// A distribution to sample floating point numbers uniformly in the closed
/// interval `[0, 1]` (including both endpoints).
///
/// See also: [`Open01`] for the open `(0, 1)`; [`Uniform`] for the half-open
/// `[0, 1)`.
///
/// # Example
/// ```rust
/// use rand::{weak_rng, Rng};
/// use rand::distributions::Closed01;
///
/// let val: f32 = weak_rng().sample(Closed01);
/// println!("f32 from [0,1]: {}", val);
/// ```
///
/// [`Uniform`]: struct.Uniform.html
/// [`Open01`]: struct.Open01.html
#[derive(Clone, Copy, Debug)]
pub struct Closed01;


macro_rules! float_impls {
    ($mod_name:ident, $ty:ty, $mantissa_bits:expr, $method_name:ident) => {
        mod $mod_name {
            use Rng;
            use distributions::{Distribution, Uniform};
            use super::{Open01, Closed01};

            const SCALE: $ty = (1u64 << $mantissa_bits) as $ty;

            impl Distribution<$ty> for Uniform {
                /// Generate a floating point number in the half-open
                /// interval `[0,1)`.
                ///
                /// See `Closed01` for the closed interval `[0,1]`,
                /// and `Open01` for the open interval `(0,1)`.
                #[inline]
                fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                    rng.$method_name()
                }
            }
            impl Distribution<$ty> for Open01 {
                #[inline]
                fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                    // add 0.5 * epsilon, so that smallest number is
                    // greater than 0, and largest number is still
                    // less than 1, specifically 1 - 0.5 * epsilon.
                    rng.$method_name() + 0.5 / SCALE
                }
            }
            impl Distribution<$ty> for Closed01 {
                #[inline]
                fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                    // rescale so that 1.0 - epsilon becomes 1.0
                    // precisely.
                    rng.$method_name() * SCALE / (SCALE - 1.0)
                }
            }
        }
    }
}
float_impls! { f64_rand_impls, f64, 52, next_f64 }
float_impls! { f32_rand_impls, f32, 23, next_f32 }


#[cfg(test)]
mod tests {
    use {Rng, RngCore, impls};
    use distributions::{Open01, Closed01};

    const EPSILON32: f32 = ::core::f32::EPSILON;
    const EPSILON64: f64 = ::core::f64::EPSILON;

    struct ConstantRng(u64);
    impl RngCore for ConstantRng {
        fn next_u32(&mut self) -> u32 {
            let ConstantRng(v) = *self;
            v as u32
        }
        fn next_u64(&mut self) -> u64 {
            let ConstantRng(v) = *self;
            v
        }
        
        fn fill_bytes(&mut self, dest: &mut [u8]) {
            impls::fill_bytes_via_u64(self, dest)
        }
    }

    #[test]
    fn floating_point_edge_cases() {
        let mut zeros = ConstantRng(0);
        assert_eq!(zeros.gen::<f32>(), 0.0);
        assert_eq!(zeros.gen::<f64>(), 0.0);
        
        let mut one = ConstantRng(1);
        assert_eq!(one.gen::<f32>(), EPSILON32);
        assert_eq!(one.gen::<f64>(), EPSILON64);
        
        let mut max = ConstantRng(!0);
        assert_eq!(max.gen::<f32>(), 1.0 - EPSILON32);
        assert_eq!(max.gen::<f64>(), 1.0 - EPSILON64);
    }

    #[test]
    fn fp_closed_edge_cases() {
        let mut zeros = ConstantRng(0);
        assert_eq!(zeros.sample::<f32, _>(Closed01), 0.0);
        assert_eq!(zeros.sample::<f64, _>(Closed01), 0.0);
        
        let mut one = ConstantRng(1);
        let one32 = one.sample::<f32, _>(Closed01);
        let one64 = one.sample::<f64, _>(Closed01);
        assert!(EPSILON32 < one32 && one32 < EPSILON32 * 1.01);
        assert!(EPSILON64 < one64 && one64 < EPSILON64 * 1.01);
        
        let mut max = ConstantRng(!0);
        assert_eq!(max.sample::<f32, _>(Closed01), 1.0);
        assert_eq!(max.sample::<f64, _>(Closed01), 1.0);
    }

    #[test]
    fn fp_open_edge_cases() {
        let mut zeros = ConstantRng(0);
        assert_eq!(zeros.sample::<f32, _>(Open01), 0.0 + EPSILON32 / 2.0);
        assert_eq!(zeros.sample::<f64, _>(Open01), 0.0 + EPSILON64 / 2.0);
        
        let mut one = ConstantRng(1);
        let one32 = one.sample::<f32, _>(Open01);
        let one64 = one.sample::<f64, _>(Open01);
        assert!(EPSILON32 < one32 && one32 < EPSILON32 * 2.0);
        assert!(EPSILON64 < one64 && one64 < EPSILON64 * 2.0);
        
        let mut max = ConstantRng(!0);
        assert_eq!(max.sample::<f32, _>(Open01), 1.0 - EPSILON32 / 2.0);
        assert_eq!(max.sample::<f64, _>(Open01), 1.0 - EPSILON64 / 2.0);
    }

    #[test]
    fn rand_open() {
        // this is unlikely to catch an incorrect implementation that
        // generates exactly 0 or 1, but it keeps it sane.
        let mut rng = ::test::rng(510);
        for _ in 0..1_000 {
            // strict inequalities
            let f: f64 = rng.sample(Open01);
            assert!(0.0 < f && f < 1.0);

            let f: f32 = rng.sample(Open01);
            assert!(0.0 < f && f < 1.0);
        }
    }

    #[test]
    fn rand_closed() {
        let mut rng = ::test::rng(511);
        for _ in 0..1_000 {
            // strict inequalities
            let f: f64 = rng.sample(Closed01);
            assert!(0.0 <= f && f <= 1.0);

            let f: f32 = rng.sample(Closed01);
            assert!(0.0 <= f && f <= 1.0);
        }
    }
}
