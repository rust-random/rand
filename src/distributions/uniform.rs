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
use distributions::{Distribution, Rand};

// ----- convenience functions -----

/// Sample values uniformly over the whole range supported by the type
/// 
/// This method has precisely two template parameters. To fix the output type,
/// use the syntax `uniform::<u32, _>(rng)`.
pub fn uniform<T: Rand<Uniform>, R: Rng+?Sized>(rng: &mut R) -> T {
    T::rand(rng, Uniform)
}

/// Sample a `char`, uniformly distributed over all Unicode scalar values,
/// i.e. all code points in the range `0...0x10_FFFF`, except for the range
/// `0xD800...0xDFFF` (the surrogate code points).  This includes
/// unassigned/reserved code points.
#[inline]
pub fn codepoint<R: Rng+?Sized>(rng: &mut R) -> char {
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

/// Sample a `char`, uniformly distributed over ASCII letters and numbers:
/// a-z, A-Z and 0-9.
#[inline]
pub fn ascii_word_char<R: Rng+?Sized>(rng: &mut R) -> char {
    use Choose;
    const GEN_ASCII_STR_CHARSET: &'static [u8] =
        b"ABCDEFGHIJKLMNOPQRSTUVWXYZ\
            abcdefghijklmnopqrstuvwxyz\
            0123456789";
    *GEN_ASCII_STR_CHARSET.choose(rng).unwrap() as char
}


// ----- Sampling distributions -----

/// Sample values uniformly over the whole range supported by the type
#[derive(Debug)]
pub struct Uniform;

/// Sample values uniformly over the half-open range [0, 1)
#[derive(Debug)]
pub struct Uniform01;

/// Sample values uniformly over the open range (0, 1)
#[derive(Debug)]
pub struct Open01;

/// Sample values uniformly over the closed range [0, 1]
#[derive(Debug)]
pub struct Closed01;


// ----- actual implementations -----

impl Distribution<isize> for Uniform {
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> isize {
        if mem::size_of::<isize>() == 4 {
            i32::rand(rng, Uniform) as isize
        } else {
            i64::rand(rng, Uniform) as isize
        }
    }
}

impl Distribution<i8> for Uniform {
    #[inline]
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> i8 {
        rng.next_u32() as i8
    }
}

impl Distribution<i16> for Uniform {
    #[inline]
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> i16 {
        rng.next_u32() as i16
    }
}

impl Distribution<i32> for Uniform {
    #[inline]
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> i32 {
        rng.next_u32() as i32
    }
}

impl Distribution<i64> for Uniform {
    #[inline]
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> i64 {
        rng.next_u64() as i64
    }
}

#[cfg(feature = "i128_support")]
impl Distribution<i128> for Uniform {
    #[inline]
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> i128 {
        rng.gen::<u128>() as i128
    }
}

impl Distribution<usize> for Uniform {
    #[inline]
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> usize {
        if mem::size_of::<usize>() == 4 {
            u32::rand(rng, Uniform) as usize
        } else {
            u64::rand(rng, Uniform) as usize
        }
    }
}

impl Distribution<u8> for Uniform {
    #[inline]
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> u8 {
        rng.next_u8()
    }
}

impl Distribution<u16> for Uniform {
    #[inline]
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> u16 {
        rng.next_u16()
    }
}

impl Distribution<u32> for Uniform {
    #[inline]
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> u32 {
        rng.next_u32()
    }
}

impl Distribution<u64> for Uniform {
    #[inline]
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> u64 {
        rng.next_u64()
    }
}

#[cfg(feature = "i128_support")]
impl Distribution<u128> for Uniform {
    #[inline]
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> u128 {
        rng.next_u128()
    }
}

impl Distribution<bool> for Uniform {
    #[inline]
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> bool {
        rng.next_u32() & 1 == 1
    }
}

impl Distribution<f32> for Uniform01 {
    /// This uses a technique described by Saito and Matsumoto at
    /// MCQMC'08. Given that the IEEE floating point numbers are
    /// uniformly distributed over [1,2), we generate a number in
    /// this range and then offset it onto the range [0,1). Our
    /// choice of bits (masking v. shifting) is arbitrary and
    /// should be immaterial for high quality generators. For low
    /// quality generators (ex. LCG), prefer bitshifting due to
    /// correlation between sequential low order bits.
    ///
    /// See:
    /// A PRNG specialized in double precision floating point numbers using
    /// an affine transition
    /// http://www.math.sci.hiroshima-u.ac.jp/~m-mat/MT/ARTICLES/dSFMT.pdf
    /// http://www.math.sci.hiroshima-u.ac.jp/~m-mat/MT/SFMT/dSFMT-slide-e.pdf
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> f32 {
        const UPPER_MASK: u32 = 0x3F800000;
        const LOWER_MASK: u32 = 0x7FFFFF;
        let tmp = UPPER_MASK | (rng.next_u32() & LOWER_MASK);
        let result: f32 = unsafe { mem::transmute(tmp) };
        result - 1.0
    }
}

impl Distribution<f64> for Uniform01 {
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> f64 {
        const UPPER_MASK: u64 = 0x3FF0000000000000;
        const LOWER_MASK: u64 = 0xFFFFFFFFFFFFF;
        let tmp = UPPER_MASK | (rng.next_u64() & LOWER_MASK);
        let result: f64 = unsafe { mem::transmute(tmp) };
        result - 1.0
    }
}

macro_rules! float_impls {
    ($scale_name:ident, $ty:ty, $mantissa_bits:expr) => {
        const $scale_name: $ty = (1u64 << $mantissa_bits) as $ty;
        
        impl Distribution<$ty> for Open01 {
            #[inline]
            fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> $ty {
                // add a small amount (specifically 2 bits below
                // the precision of f64/f32 at 1.0), so that small
                // numbers are larger than 0, but large numbers
                // aren't pushed to/above 1.
                let x: $ty = Rand::rand(rng, Uniform01);
                x + 0.25 / $scale_name
            }
        }
        impl Distribution<$ty> for Closed01 {
            #[inline]
            fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> $ty {
                // rescale so that 1.0 - epsilon becomes 1.0
                // precisely.
                let x: $ty = Rand::rand(rng, Uniform01);
                x * $scale_name / ($scale_name - 1.0)
            }
        }
    }
}
float_impls! { SCALE_F64, f64, 53 }
float_impls! { SCALE_F32, f32, 24 }


#[cfg(test)]
mod tests {
    use {Rng, thread_rng, iter};
    use distributions::{Rand, uniform, Uniform, Uniform01, Open01, Closed01};
    use distributions::uniform::{codepoint, ascii_word_char};
    
    #[test]
    fn test_integers() {
        let mut rng = ::test::rng();
        
        let _: i32 = Rand::rand(&mut rng, Uniform);
        let _ = i32::rand(&mut rng, Uniform);
        
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
    
    #[test]
    fn test_chars() {
        let mut rng = ::test::rng();
        
        let _ = codepoint(&mut rng);
        let c = ascii_word_char(&mut rng);
        assert!((c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z'));
        
        let word: String = iter(&mut rng).take(5).map(|rng| ascii_word_char(rng)).collect();
        assert_eq!(word.len(), 5);
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
        let a: f64 = Rand::rand(&mut r, Uniform01);
        let b = f64::rand(&mut r, Uniform01);
        assert!(0.0 <= a && a < 1.0);
        assert!(0.0 <= b && b < 1.0);
    }

    #[test]
    fn floating_point_edge_cases() {
        // FIXME: this message and test predates this repo; message suggests
        // test is supposed to be ==; using != is pretty useless
        // the test for exact equality is correct here.
        assert!(f64::rand(&mut ConstantRng(0xffff_ffff), Uniform01) != 1.0);
        assert!(f64::rand(&mut ConstantRng(0xffff_ffff_ffff_ffff), Uniform01) != 1.0);
    }

    #[test]
    fn rand_open() {
        // this is unlikely to catch an incorrect implementation that
        // generates exactly 0 or 1, but it keeps it sane.
        let mut rng = thread_rng();
        for _ in 0..1_000 {
            // strict inequalities
            let f = f64::rand(&mut rng, Open01);
            assert!(0.0 < f && f < 1.0);

            let f = f32::rand(&mut rng, Open01);
            assert!(0.0 < f && f < 1.0);
        }
    }

    #[test]
    fn rand_closed() {
        let mut rng = thread_rng();
        for _ in 0..1_000 {
            // strict inequalities
            let f = f64::rand(&mut rng, Closed01);
            assert!(0.0 <= f && f <= 1.0);

            let f = f32::rand(&mut rng, Closed01);
            assert!(0.0 <= f && f <= 1.0);
        }
    }
}
