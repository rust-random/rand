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

use core::char;
use core::mem;

use Rng;
use distributions::Distribution;
use utils::FloatConversions;

// ----- convenience functions -----

/// Sample values uniformly over the whole range supported by the type
/// 
/// This method has precisely two template parameters. To fix the output type,
/// use the syntax `uniform::<u32, _>(rng)`.
pub fn uniform<T, R: Rng+?Sized>(rng: &mut R) -> T where Uniform: Distribution<T> {
    Uniform.sample(rng)
}

/// Sample a `char`, uniformly distributed over all Unicode scalar values,
/// i.e. all code points in the range `0...0x10_FFFF`, except for the range
/// `0xD800...0xDFFF` (the surrogate code points).  This includes
/// unassigned/reserved code points.
/// 
/// TODO: should this be removed in favour of a distribution?
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
/// 
/// TODO: should this be removed in favour of `AsciiWordChar`?
#[inline]
pub fn ascii_word_char<R: Rng+?Sized>(rng: &mut R) -> char {
    use sequences::Choose;
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

/// Sample values uniformly from the ASCII ranges z-a, A-Z, and 0-9.
#[derive(Debug)]
pub struct AsciiWordChar;


// ----- actual implementations -----

impl Distribution<isize> for Uniform {
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> isize {
        if mem::size_of::<isize>() == 4 {
            Distribution::<i32>::sample(&Uniform, rng) as isize
        } else {
            Distribution::<i64>::sample(&Uniform, rng) as isize
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
        rng.next_u128() as i128
    }
}

impl Distribution<usize> for Uniform {
    #[inline]
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> usize {
        if mem::size_of::<usize>() == 4 {
            Distribution::<u32>::sample(&Uniform, rng) as usize
        } else {
            Distribution::<u64>::sample(&Uniform, rng) as usize
        }
    }
}

impl Distribution<u8> for Uniform {
    #[inline]
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> u8 {
        rng.next_u32() as u8
    }
}

impl Distribution<u16> for Uniform {
    #[inline]
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> u16 {
        rng.next_u32() as u16
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
        // We can compare against an arbitrary bit of an u32 to get a bool.
        // Because the least significant bits of a lower quality RNG can have
        // simple patterns, we compare against the most significant bit. This is
        // easiest done using a sign test.
        (rng.next_u32() as i32) < 0
    }
}

macro_rules! float_impls {
    ($ty:ty, $next_u:path) => {
        impl Distribution<$ty> for Uniform01 {
            fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> $ty {
                let x = $next_u(rng);
                x.closed_open01()
            }
        }

        impl Distribution<$ty> for Closed01 {
            fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> $ty {
                // The problem with a closed range over [0,1] is that it needs
                // 2^n+1 samples to generate a uniform distribution. Which is
                // difficult, as it means we either have to reject about half
                // the generated random numbers, or just not include one number
                // in the distribution. That is why, instead of a closed range,
                // we actually sample from the half-open range (0,1].
                //
                // Floating-point numbers have more precision near zero. This
                // means for a f32 that only 1 in 2^32 samples will give exactly
                // 0.0. But 1 in 2^23 will give exactly 1.0 due to rounding.
                // Because the chance to sample 0.0 is so low, this half-open
                // range is a very good appoximation of a closed range.
                let x = $next_u(rng);
                x.open_closed01()
            }
        }

        impl Distribution<$ty> for Open01 {
            // Sample from the open range (0,1).
            // This uses the rejection method: use `closed_open01`, and if the
            // result is 0.0, reject the result and try again.
            fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> $ty {
                let mut x = 0;
                while x == 0 { // 0 converts to 0.0
                    x = $next_u(rng);
                }
                x.closed_open01()
            }
        }
    }
}
float_impls! { f32, Rng::next_u32 }
float_impls! { f64, Rng::next_u64 }


impl Distribution<char> for AsciiWordChar {
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> char {
        ascii_word_char(rng)
    }
}


#[cfg(test)]
mod tests {
    use {thread_rng, iter};
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

    #[test]
    fn test_f64() {
        let mut r = thread_rng();
        let a: f64 = Rand::rand(&mut r, Uniform01);
        let b = f64::rand(&mut r, Uniform01);
        assert!(0.0 <= a && a < 1.0);
        assert!(0.0 <= b && b < 1.0);
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
