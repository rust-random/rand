// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Generating uniformly distributed numbers

use std::char;
use std::mem;

use Rng;

// ----- convenience functions -----

/// Sample values uniformly over the whole range supported by the type
/// 
/// This method has precisely two template parameters. To fix the output type,
/// use the syntax `uniform::<u32, _>(rng)`.
pub fn uniform<T: SampleUniform, R: Rng>(rng: &mut R) -> T {
    T::sample_uniform(rng)
}

/// Sample values uniformly over the half-open range [0, 1)
/// 
/// This method has precisely two template parameters. To fix the output type,
/// use the syntax `uniform01::<f64, _>(rng)`.
pub fn uniform01<T: SampleUniform01, R: Rng>(rng: &mut R) -> T {
    T::sample_uniform01(rng)
}

/// Sample values uniformly over the open range (0, 1)
/// 
/// This method has precisely two template parameters. To fix the output type,
/// use the syntax `open01::<f64, _>(rng)`.
pub fn open01<T: SampleOpen01, R: Rng>(rng: &mut R) -> T {
    T::sample_open01(rng)
}

/// Sample values uniformly over the closed range [0, 1]
/// 
/// This method has precisely two template parameters. To fix the output type,
/// use the syntax `closed01::<f64, _>(rng)`.
pub fn closed01<T: SampleClosed01, R: Rng>(rng: &mut R) -> T {
    T::sample_closed01(rng)
}

/// Sample a `char`, uniformly distributed over all Unicode scalar values,
/// i.e. all code points in the range `0...0x10_FFFF`, except for the range
/// `0xD800...0xDFFF` (the surrogate code points).  This includes
/// unassigned/reserved code points.
#[inline]
pub fn codepoint<R: Rng>(rng: &mut R) -> char {
    // a char is 21 bits
    const CHAR_MASK: u32 = 0x001f_ffff;
    loop {
        // Rejection sampling. About 0.2% of numbers with at most
        // 21-bits are invalid codepoints (surrogates), so this
        // will succeed first go almost every time.
        match char::from_u32(rng.next_u32() & CHAR_MASK) {
            Some(c) => return c,
            None => {}
        }
    }
}


// ----- Sampling traits -----

/// Sample values uniformly over the whole range supported by the type
pub trait SampleUniform: Sized {
    /// Sample a value using an RNG
    fn sample_uniform<R: Rng>(rng: &mut R) -> Self;
}

/// Sample values uniformly over the half-open range [0, 1)
pub trait SampleUniform01: Sized {
    /// Sample a value using an RNG
    fn sample_uniform01<R: Rng>(rng: &mut R) -> Self;
}

/// Sample values uniformly over the open range (0, 1)
pub trait SampleOpen01: Sized {
    /// Sample a value using an RNG
    fn sample_open01<R: Rng>(rng: &mut R) -> Self;
}

/// Sample values uniformly over the closed range [0, 1]
pub trait SampleClosed01: Sized {
    /// Sample a value using an RNG
    fn sample_closed01<R: Rng>(rng: &mut R) -> Self;
}


// ----- actual implementations -----

impl SampleUniform for isize {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> isize {
        if mem::size_of::<isize>() == 4 {
            i32::sample_uniform(rng) as isize
        } else {
            i64::sample_uniform(rng) as isize
        }
    }
}

impl SampleUniform for i8 {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> i8 {
        rng.next_u32() as i8
    }
}

impl SampleUniform for i16 {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> i16 {
        rng.next_u32() as i16
    }
}

impl SampleUniform for i32 {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> i32 {
        rng.next_u32() as i32
    }
}

impl SampleUniform for i64 {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> i64 {
        rng.next_u64() as i64
    }
}

#[cfg(feature = "i128_support")]
impl SampleUniform for i128 {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> i128 {
        rng.gen::<u128>() as i128
    }
}

impl SampleUniform for usize {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> usize {
        if mem::size_of::<usize>() == 4 {
            u32::sample_uniform(rng) as usize
        } else {
            u64::sample_uniform(rng) as usize
        }
    }
}

impl SampleUniform for u8 {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> u8 {
        rng.next_u32() as u8
    }
}

impl SampleUniform for u16 {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> u16 {
        rng.next_u32() as u16
    }
}

impl SampleUniform for u32 {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> u32 {
        rng.next_u32()
    }
}

impl SampleUniform for u64 {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> u64 {
        rng.next_u64()
    }
}

#[cfg(feature = "i128_support")]
impl SampleUniform for u128 {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> u128 {
        ((rng.next_u64() as u128) << 64) | (rng.next_u64() as u128)
    }
}

impl SampleUniform for bool {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> bool {
        rng.next_u32() & 1 == 1
    }
}


macro_rules! float_impls {
    ($scale_name:ident, $ty:ty, $mantissa_bits:expr, $method_name:ident) => {
        const $scale_name: $ty = (1u64 << $mantissa_bits) as $ty;
        
        impl SampleUniform01 for $ty {
            #[inline]
            fn sample_uniform01<R: Rng>(rng: &mut R) -> $ty {
                rng.$method_name()
            }
        }
        impl SampleOpen01 for $ty {
            #[inline]
            fn sample_open01<R: Rng>(rng: &mut R) -> $ty {
                // add a small amount (specifically 2 bits below
                // the precision of f64/f32 at 1.0), so that small
                // numbers are larger than 0, but large numbers
                // aren't pushed to/above 1.
                uniform01::<$ty, _>(rng) + 0.25 / $scale_name
            }
        }
        impl SampleClosed01 for $ty {
            #[inline]
            fn sample_closed01<R: Rng>(rng: &mut R) -> $ty {
                // rescale so that 1.0 - epsilon becomes 1.0
                // precisely.
                uniform01::<$ty, _>(rng) * $scale_name / ($scale_name - 1.0)
            }
        }
    }
}
float_impls! { SCALE_F64, f64, 53, next_f64 }
float_impls! { SCALE_F32, f32, 24, next_f32 }


#[cfg(test)]
mod tests {
    use {Rng, thread_rng};
    use dist::{uniform};
    use dist::uniform::SampleUniform;
    use dist::{uniform01, open01, closed01};
    
    #[test]
    fn test_integers() {
        let mut rng = ::test::rng();
        
        let _: i32 = SampleUniform::sample_uniform(&mut rng);
        let _: i32 = i32::sample_uniform(&mut rng);
        
        let _: isize = uniform(&mut rng);
        let _: i8 = uniform(&mut rng);
        let _: i16 = uniform(&mut rng);
        let _: i32 = uniform(&mut rng);
        let _: i64 = uniform(&mut rng);
        #[cfg(feature = "i128_support")]
        let _: i128 = uniform(&mut rng);
        
        let _: usize = uniform(&mut rng);
        let _: u8 = uniform(&mut rng);
        let _: u16 = uniform(&mut rng);
        let _: u32 = uniform(&mut rng);
        let _: u64 = uniform(&mut rng);
        #[cfg(feature = "i128_support")]
        let _: u128 = uniform(&mut rng);
    }

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
    fn test_f64() {
        let mut r = thread_rng();
        let a: f64 = uniform01(&mut r);
        let b = uniform01::<f64, _>(&mut r);
        assert!(0.0 <= a && a < 1.0);
        assert!(0.0 <= b && b < 1.0);
    }

    #[test]
    fn floating_point_edge_cases() {
        // FIXME: this message and test predates this repo; message suggests
        // test is supposed to be ==; using != is pretty useless
        // the test for exact equality is correct here.
        assert!(uniform01::<f64, _>(&mut ConstantRng(0xffff_ffff)) != 1.0);
        assert!(uniform01::<f64, _>(&mut ConstantRng(0xffff_ffff_ffff_ffff)) != 1.0);
    }

    #[test]
    fn rand_open() {
        // this is unlikely to catch an incorrect implementation that
        // generates exactly 0 or 1, but it keeps it sane.
        let mut rng = thread_rng();
        for _ in 0..1_000 {
            // strict inequalities
            let f = open01::<f64, _>(&mut rng);
            assert!(0.0 < f && f < 1.0);

            let f = open01::<f32, _>(&mut rng);
            assert!(0.0 < f && f < 1.0);
        }
    }

    #[test]
    fn rand_closed() {
        let mut rng = thread_rng();
        for _ in 0..1_000 {
            // strict inequalities
            let f = closed01::<f64, _>(&mut rng);
            assert!(0.0 <= f && f <= 1.0);

            let f = closed01::<f32, _>(&mut rng);
            assert!(0.0 <= f && f <= 1.0);
        }
    }
}
