// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A collection of utility functions
//!
//! This module exposes some utility functions used internally by the `Rand`
//! crate. They are not the intended or most ergonomic way to use the library.
//!
//! The `FloatConversions` trait provides the building blocks to convert a
//! random integer to a IEEE floating point number uniformly distributed over a
//! some range.

use core::mem;

trait FloatBitOps {
    type F;

    /// Helper function to combine the fraction, exponent and sign into a float.
    /// `self` includes the bits from the fraction and sign.
    fn binor_exp(self, exponent: i32) -> Self::F;
}

impl FloatBitOps for u32 {
    type F = f32;
    #[inline(always)]
    fn binor_exp(self, exponent: i32) -> f32 {
        // The exponent is encoded using an offset-binary representation,
        // with the zero offset being 127
        let exponent_bits = ((127 + exponent) as u32) << 23;
        unsafe { mem::transmute(self | exponent_bits) }
    }
}

impl FloatBitOps for u64 {
    type F = f64;
    #[inline(always)]
    fn binor_exp(self, exponent: i32) -> f64 {
        // The exponent is encoded using an offset-binary representation,
        // with the zero offset being 1023
        let exponent_bits = ((1023 + exponent) as u64) << 52;
        unsafe { mem::transmute(self | exponent_bits) }
    }
}

/// Convert a random integer to a uniformly distributed floating point number.
pub trait FloatConversions {
    type F;

    /// Convert a random integer to a floating point number sampled from the
    /// uniformly distributed half-open range [0,1).
    /// The precision gets higher closer to zero, up to 2^-32 for f32
    /// and 2^-64 for f64.
    fn closed_open01(self) -> Self::F;

    /// Convert a random integer to a floating point number sampled from the
    /// uniformly distributed half-open range (0,1].
    /// The precision gets higher closer to zero, up to 2^-32 for f32
    /// and 2^-64 for f64.
    fn open_closed01(self) -> Self::F;

    /// Convert a random integer to a floating point number sampled from the
    /// uniformly distributed half-open range [-1,1).
    /// The precision gets higher closer to zero, up to 2^-32 for f32
    /// and 2^-64 for f64.
    fn closed_open11(self) -> Self::F;

    /// Convert a random integer to a floating point number sampled from the
    /// uniformly distributed half-open range [0,1).
    /// The precision is fixed, with 2^-23 for f32 and 2^-52 for f64.
    /// This leaves a couple of the random bits available for other purposes
    /// (the 9 least significant bits for f32, and 12 for f64).
    fn closed_open01_fixed(self) -> Self::F;

    /// Convert a random integer to a floating point number sampled from the
    /// uniformly distributed half-open range (0,1].
    /// The precision is fixed, with 2^-23 for f32 and 2^-52 for f64.
    /// This leaves a couple of the random bits available for other purposes
    /// (the 9 least significant bits for f32, and 12 for f64).
    fn open_closed01_fixed(self) -> Self::F;

    /// Convert a random integer to a floating point number sampled from the
    /// uniformly distributed half-open range [-1,1).
    /// The precision is fixed, with 2^-22 for f32 and 2^-51 for f64.
    /// This leaves a couple of the random bits available for other purposes
    /// (the 9 least significant bits for f32, and 12 for f64).
    fn closed_open11_fixed(self) -> Self::F;
}

macro_rules! float_impls {
    ($ty:ty, $uty:ty, $FLOAT_SIZE:expr, $FRACTION_BITS:expr,
     $FRACTION_MASK:expr, $EXPONENT_BIAS:expr, $next_u:path) => {

        impl FloatConversions for $uty {
            type F = $ty;

            /// Convert a random number to a floating point number sampled from
            /// the uniformly distributed half-open range [0,1).
            ///
            /// We fill the fractional part of the f32 with 23 random bits.
            /// The trick to generate a uniform distribution over [0,1) is to
            /// fill the exponent with the -log2 of the remaining random bits. A
            /// simpler alternative to -log2 is to count the number of trailing
            /// zero's of the random bits, add 1, and negate the result.
            ///
            /// Each exponent is responsible for a piece of the distribution
            /// between [0,1). The exponent -1 fills the part [0.5,1). -2 fills
            /// [0.25,0.5). The lowest exponent we can get is -10. So a problem
            /// with this method is that we can not fill the part between zero
            /// and the part from -10. The solution is to treat numbers with an
            /// exponent of -10 as if they have -9 as exponent, and substract
            /// 2^-9.
            #[inline(always)]
            fn closed_open01(self) -> $ty {
                const MIN_EXPONENT: i32 = $FRACTION_BITS - $FLOAT_SIZE;
                #[allow(non_snake_case)]
                let ADJUST: $ty = (0 as $uty).binor_exp(MIN_EXPONENT);
                                  // 2^MIN_EXPONENT

                // Use the last 23 bits to fill the fraction
                let fraction = self & $FRACTION_MASK;
                // Use the remaing (first) 9 bits for the exponent
                let exp = $FRACTION_BITS - 1
                          - ((self & !$FRACTION_MASK).trailing_zeros() as i32);
                if exp < MIN_EXPONENT {
                    return fraction.binor_exp(MIN_EXPONENT) - ADJUST;
                }
                fraction.binor_exp(exp)
            }

            /// Convert a random number to a floating point number sampled from
            /// the uniformly distributed chalf-open range (0,1].
            ///
            /// This method is similar to `closed_open01`, with one extra step:
            /// If the fractional part ends up as zero, add 1 to the exponent in
            /// 50% of the cases. This changes 0.5 to 1.0, 0.25 to 0.5, etc.
            ///
            /// The chance to select these numbers that staddle the boundery
            /// between exponents is 33% to high in `closed_open01`
            /// (e.g. 33%*2^-23 for 0.5f32). The reason is that with 0.5 as
            /// example the distance to the next number is 2^-23, but to the
            /// previous number 2^-24. With the adjustment they have exactly the
            /// right chance of getting sampled.
            #[inline(always)]
            fn open_closed01(self) -> $ty {
                const MIN_EXPONENT: i32 = $FRACTION_BITS - $FLOAT_SIZE;
                #[allow(non_snake_case)]
                let ADJUST: $ty = (0 as $uty).binor_exp(MIN_EXPONENT);
                                  // 2^MIN_EXPONENT

                // Use the last 23 bits to fill the fraction
                let fraction = self & $FRACTION_MASK;
                // Use the remaing (first) 9 bits for the exponent
                let mut exp = $FRACTION_BITS - 1
                              - ((self & !$FRACTION_MASK).trailing_zeros() as i32);
                if fraction == 0 {
                    // Shift the exponent in about 50% of the samples, based on
                    // one of the unused bits for the exponent.
                    // Shift uncondinionally for the lowest exponents, because
                    // there are no more random bits left.
                    if (exp <= MIN_EXPONENT) ||
                       (self & 1 << ($FLOAT_SIZE - 1) != 0) {
                        exp += 1;
                    }
                } else if exp < MIN_EXPONENT {
                    return fraction.binor_exp(MIN_EXPONENT) - ADJUST;
                }
                fraction.binor_exp(exp)
            }

            /// Convert a random number to a floating point number sampled from
            /// the uniformly distributed half-open range [-1,1).
            ///
            /// This uses the same method as `closed_open01`. One of the random
            /// bits that it uses for the exponent, is now used as a sign bit.
            ///
            /// This samples numbers from the range (-1,-0] and [0,1). Ideally
            /// we would not sample -0.0, but include -1.0. That is why for
            /// negative numbers we use the extra step from `open01`.
            #[inline(always)]
            fn closed_open11(self) -> $ty {
                const MIN_EXPONENT: i32 = $FRACTION_BITS - $FLOAT_SIZE + 1;
                const SIGN_BIT: $uty = 1 << ($FLOAT_SIZE - 1);
                #[allow(non_snake_case)]
                let ADJUST: $ty = (0 as $uty).binor_exp(MIN_EXPONENT);
                                  // 2^MIN_EXPONENT

                // Use the last 23 bits to fill the fraction, and the first bit
                // as sign
                let fraction = self & ($FRACTION_MASK | SIGN_BIT);
                // Use the remaing 8 bits for the exponent
                let mut exp = $FRACTION_BITS -
                              (((self & !$FRACTION_MASK) << 1).trailing_zeros() as i32);
                if fraction == SIGN_BIT {
                    // Shift the exponent in about 50% of the samples, based on
                    // one of the unused bits for the exponent.
                    // Shift uncondinionally for the lowest exponents, because
                    // there are no more random bits left.
                    if (exp <= MIN_EXPONENT) ||
                       (self & 1 << ($FLOAT_SIZE - 2) != 0) {
                        exp += 1;
                    }
                } else if exp < MIN_EXPONENT {
                    let result: $ty = fraction.binor_exp(MIN_EXPONENT);
                    match fraction & SIGN_BIT == SIGN_BIT {
                        false => return result - ADJUST,
                        true => return result + ADJUST,
                    };
                }
                fraction.binor_exp(exp)
            }

            /// This uses a technique described by Saito and Matsumoto at
            /// MCQMC'08. Given that the IEEE floating point numbers are
            /// uniformly distributed over [1,2), we generate a number in this
            /// range and then offset it onto the range [0,1). Our choice of
            /// bits (masking v. shifting) is arbitrary and should be immaterial
            /// for high quality generators. For low quality generators
            /// (ex. LCG), prefer bitshifting due to correlation between
            /// sequential low order bits.
            ///
            /// See:
            /// A PRNG specialized in double precision floating point numbers
            /// using an affine transition
            /// http://www.math.sci.hiroshima-u.ac.jp/~m-mat/MT/ARTICLES/dSFMT.pdf
            /// http://www.math.sci.hiroshima-u.ac.jp/~m-mat/MT/SFMT/dSFMT-slide-e.pdf
            #[inline(always)]
            fn closed_open01_fixed(self) -> $ty {
                const EXPONENT: i32 = 0;
                let fraction = self >> ($FLOAT_SIZE - $FRACTION_BITS);
                fraction.binor_exp(EXPONENT) - 1.0
            }

            // Similar to `closed_open01_fixed`, with one modification. After
            // converting to a float but before substracting -1.0, we want to
            // shift every number one place to the next floating point number
            // (e.g. +1 ulp). Thanks to how floating points a represented, this
            // is as simple as adding 1 to the integer representation.
            // Because we inline the `binor_exp` function, this looks more
            // different than it really is.
            #[inline(always)]
            fn open_closed01_fixed(self) -> $ty {
                let exponent_bits: $uty = $EXPONENT_BIAS << $FRACTION_BITS + 0;
                let fraction = self >> ($FLOAT_SIZE - $FRACTION_BITS);
                let bits = fraction | exponent_bits;
                let float: $ty = unsafe { mem::transmute(bits + 1) };
                float - 1.0
            }

            /// Like `closed_open01_fixed`, but generate a number in the range
            /// [2,4) and offset it onto the range [-1,1).
            #[inline(always)]
            fn closed_open11_fixed(self) -> $ty {
                const EXPONENT: i32 = 1;
                let fraction = self >> ($FLOAT_SIZE - $FRACTION_BITS);
                fraction.binor_exp(EXPONENT) - 3.0
           }
        }
    }
}
float_impls! { f32, u32, 32, 23, 0x7f_ffff, 127, Rng::next_u32 }
float_impls! { f64, u64, 64, 52, 0xf_ffff_ffff_ffff, 1023, Rng::next_u64 }


#[cfg(test)]
mod tests {
    use super::FloatConversions;
    use distributions::uniform;

    #[test]
    fn closed_open01_edge_cases() {
        // Test that the distribution is a half-open range over [0,1).
        // These constants happen to generate the lowest and highest floats in
        // the range.
        assert!(0u32.closed_open01() == 0.0);
        assert!(0xffff_ffffu32.closed_open01() == 0.99999994);

        assert!(0u64.closed_open01() == 0.0);
        assert!(0xffff_ffff_ffff_ffffu64.closed_open01() == 0.9999999999999999);
    }

    #[test]
    fn open_closed01_edge_cases() {
        // Test that the distribution is a half-open range over (0,1].
        // These constants happen to generate the lowest and highest floats in
        // the range.
        assert!(1u32.open_closed01() == 2.3283064e-10); // 2^-32
        assert!(0xff80_0000u32.open_closed01() == 1.0);

        assert!(1u64.open_closed01() == 5.421010862427522e-20); // 2^-64
        assert!(0xfff0_0000_0000_0000u64.open_closed01() == 1.0);
    }

    #[test]
    fn closed_open11_edge_cases() {
        // Test that the distribution is a half-open range over [-1,1).
        // These constants happen to generate the lowest and highest floats in
        // the range.
        assert!(0xff80_0000u32.closed_open11() == -1.0);
        assert!(0x7fff_ffffu32.closed_open11() == 0.99999994); // 1 - 2^-24

        assert!(0xfff0_0000_0000_0000u64.closed_open11() == -1.0);
        assert!(0x7fff_ffff_ffff_ffffu64.closed_open11() == 0.9999999999999999);
    }

    #[test]
    fn closed_open01_fixed_edge_cases() {
        // Test that the distribution is a half-open range over [0,1).
        // These constants happen to generate the lowest and highest floats in
        // the range.
        let mut rng = ::test::rng();
        let mut bits: u32 = uniform(&mut rng);
        bits = bits & 0x1ff; // 9 bits with no influence

        assert!((bits | 0).closed_open01_fixed() == 0.0);
        assert!((bits | 0xfffffe00).closed_open01_fixed()
                == 0.9999999); // 1 - 2^-23

        let mut bits: u64 = uniform(&mut rng);
        bits = bits & 0xfff; // 12 bits with no influence

        assert!((bits | 0).closed_open01_fixed() == 0.0);
        assert!((bits | 0xffff_ffff_ffff_f000).closed_open01_fixed() ==
                0.9999999999999998); // 1 - 2^-52
    }

    #[test]
    fn open_closed01_fixed_edge_cases() {
        // Test that the distribution is a half-open range over [0,1).
        // These constants happen to generate the lowest and highest floats in
        // the range.
        let mut rng = ::test::rng();
        let mut bits: u32 = uniform(&mut rng);
        bits = bits & 0x1ff; // 9 bits with no influence

        assert!((bits | 0).open_closed01_fixed() == 1.1920929e-7); // 2^-23
        assert!((bits | 0xfffffe00).open_closed01_fixed() == 1.0);

        let mut bits: u64 = uniform(&mut rng);
        bits = bits & 0xfff; // 12 bits with no influence

        assert!((bits | 0).open_closed01_fixed() ==
                2.220446049250313e-16); // 2^-52
        assert!((bits | 0xffff_ffff_ffff_f000).open_closed01_fixed() == 1.0);
    }

    #[test]
    fn closed_open11_fixed_edge_cases() {
        // Test that the distribution is a half-open range over [0,1).
        // These constants happen to generate the lowest and highest floats in
        // the range.
        let mut rng = ::test::rng();
        let mut bits: u32 = uniform(&mut rng);
        bits = bits & 0x1ff; // 9 bits with no influence

        assert!((bits | 0).closed_open11_fixed() == -1.0);
        assert!((bits | 0xfffffe00).closed_open11_fixed()
                == 0.99999976); // 1 - 2^-22

        let mut bits: u64 = uniform(&mut rng);
        bits = bits & 0xfff; // 12 bits with no influence

        assert!((bits | 0).closed_open11_fixed() == -1.0);
        assert!((bits | 0xffff_ffff_ffff_f000).closed_open11_fixed() ==
                0.9999999999999996); // 1 - 2^-51
    }
}
