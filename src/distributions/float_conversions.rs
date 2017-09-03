// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Convert a random int to a float in the range [0,1]

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

pub trait FloatConversions {
    type F;

    /// Convert a random number to a floating point number sampled from the
    /// uniformly distributed half-open range [0,1).
    /// Closer to zero the distribution gains more precision, up to
    /// 2^-32 for f32 and 2^-64 for f64.
    fn uniform01(self) -> Self::F;

    /// Convert a random number to a floating point number sampled from the
    /// uniformly distributed closed range [0,1].
    /// Closer to zero the distribution gains more precision, up to
    /// 2^-32 for f32 and 2^-64 for f64.
    fn closed01(self) -> Self::F;

    /// Convert a random number to a floating point number sampled from the
    /// uniformly distributed half-open range [-1,1).
    /// Closer to zero the distribution gains more precision, up to
    /// 2^-32 for f32 and 2^-64 for f64.
    fn uniform11(self) -> Self::F;
}

macro_rules! float_impls {
    ($ty:ty, $uty:ty, $FLOAT_SIZE:expr, $FRACTION_BITS:expr,
     $FRACTION_MASK:expr, $next_u:path) => {

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
            fn uniform01(self) -> $ty {
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
            /// the uniformly distributed closed range [0,1].
            ///
            /// The problem with a closed range over [0,1] is that the chance to
            /// sample 1.0 exactly is 2^n+1. Which is difficult, as it is not a
            /// power of two. Instead of a closed range, we actually sample from
            /// the half-open range (0,1].
            ///
            /// Floating-point numbers have more precision near zero. This means
            /// for a f32 that only 1 in 2^32 samples will give exactly 0.0. But
            /// 1 in 2^23 will give exactly 1.0 due to rounding. Because the
            /// chance to sample 0.0 is so low, this half-open range is a very
            /// good appoximation of a closed range.
            ///
            /// This method is similar to `Uniform01`, with one extra step:
            /// If the fractional part ends up as zero, add 1 to the exponent in
            /// 50% of the cases. This changes 0.5 to 1.0, 0.25 to 0.5, etc.
            ///
            /// The chance to select these numbers that staddle the boundery
            /// between exponents is 33% to high in `Uniform01` (e.g. 33%*2^-23
            /// for 0.5f32). The reason is that with 0.5 as example the distance
            /// to the next number is 2^-23, but to the previous number 2^-24.
            /// With the adjustment they have exactly the right chance of
            /// getting sampled.
            #[inline(always)]
            fn closed01(self) -> $ty {
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
                    if (exp > MIN_EXPONENT) &&
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
            /// This uses the same method as `uniform01`. One of the random bits
            /// that it uses for the exponent, is now used as a sign bit.
            ///
            /// This samples numbers from the range (-1,-0] and [0,1). Ideally
            /// we would not sample -0.0, but include -1.0. That is why for
            /// negative numbers we use the extra step from `open01`.
            #[inline(always)]
            fn uniform11(self) -> $ty {
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
                    if (exp > MIN_EXPONENT) &&
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
        }
    }
}
float_impls! { f32, u32, 32, 23, 0x7FFFFF, Rng::next_u32 }
float_impls! { f64, u64, 64, 52, 0xFFFFFFFFFFFFF, Rng::next_u64 }


#[cfg(test)]
mod tests {
    use super::FloatConversions;

    #[test]
    fn uniform01_edge_cases() {
        // Test that the distribution is a half-open range over [0,1).
        // These constants happen to generate the lowest and highest floats in
        // the range.
        assert!(0u32.uniform01() == 0.0);
        assert!(0xffff_ffffu32.uniform01() == 0.99999994);

        assert!(0u64.uniform01() == 0.0);
        assert!(0xffff_ffff_ffff_ffffu64.uniform01() == 0.9999999999999999);
    }

    #[test]
    fn closed01_edge_cases() {
        // Test that the distribution is a half-open range over (0,1].
        // These constants happen to generate the lowest and highest floats in
        // the range.
        assert!(1u32.closed01() == 2.3283064e-10); // 2^-32
        assert!(0xff80_0000u32.closed01() == 1.0);

        assert!(1u64.closed01() == 5.421010862427522e-20); // 2^-64
        assert!(0xfff0_0000_0000_0000u64.closed01() == 1.0);
    }

    #[test]
    fn uniform11_edge_cases() {
        // Test that the distribution is a half-open range over [-1,1).
        // These constants happen to generate the lowest and highest floats in
        // the range.
        assert!(0xff80_0000u32.uniform11() == -1.0);
        assert!(0x7fff_ffffu32.uniform11() == 0.99999994);

        assert!(0xfff0_0000_0000_0000u64.uniform11() == -1.0);
        assert!(0x7fff_ffff_ffff_ffffu64.uniform11() == 0.9999999999999999);
    }
}
