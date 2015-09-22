// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The Xorshift family of random number generators.
use std::num::Wrapping as w;

use {Rng, SeedableRng, Rand, w32, w64};

/// A Xorshift128+[1] random number generator.
///
/// The Xorshift128+ algorithm is not suitable for cryptographic purposes
/// but is very fast. If you do not know for sure that it fits your
/// requirements, use a more secure one such as `IsaacRng` or `OsRng`.
/// This variant uses 64bit arithmetic and is appropriated for 64bit architectures.
/// Compared to Xorshift128 this variant also produces a higher quality distribution.
///
/// [1]: Vigna, S. (2014). [Further scramblings of 
/// Marsaglia's xorshift generators](http://arxiv.org/pdf/1404.0390.pdf).
/// arXiv preprint arXiv:1404.0390.
#[derive(Copy, Clone)]
pub struct XorShiftPlusRng {
    s: [w64; 2]
}

impl XorShiftPlusRng {
    /// Creates a new XorShiftPlusRng instance which is not seeded.
    ///
    /// The initial values of this RNG are constants, so all generators created
    /// by this function will yield the same stream of random numbers. It is
    /// highly recommended that this is created through `SeedableRng` instead of
    /// this function
    pub fn new_unseeded() -> XorShiftPlusRng {
        XorShiftPlusRng {
            s: [w(0x193a6754a8a7d469), w(0x97830e05113ba7bb)]
        }
    }
}

impl Rng for XorShiftPlusRng {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        self.next_u64() as u32
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        let mut s1 = self.s[0];
        let s0 = self.s[1];
        self.s[0] = s0;
        s1 = s1 ^ (s1 << 23); // a
        self.s[1] = s1 ^ s0 ^ (s1 >> 17) ^ (s0 >> 26); // b, c
        (self.s[1] + s0).0
    }
}

impl SeedableRng<[u64; 2]> for XorShiftPlusRng {
    /// Reseed an XorShiftPlusRng. This will panic if `seed` is entirely 0.
    fn reseed(&mut self, seed: [u64; 2]) {
        assert!(seed != [0, 0],
                "XorShiftPlusRng.reseed called with an all zero seed.");

        self.s = [w(seed[0]), w(seed[1])];
    }

    /// Create a new XorShiftPlusRng. This will panic if `seed` is entirely 0.
    fn from_seed(seed: [u64; 2]) -> XorShiftPlusRng {
        assert!(seed != [0, 0],
                "XorShiftPlusRng::from_seed called with an all zero seed.");

        XorShiftPlusRng {
            s: [w(seed[0]), w(seed[1])]
        }
    }
}

impl Rand for XorShiftPlusRng {
    fn rand<R: Rng>(rng: &mut R) -> XorShiftPlusRng {
        let mut seed: (u64, u64) = rng.gen();
        while seed == (0, 0) {
            seed = rng.gen();
        }
        XorShiftPlusRng { s: [w(seed.0), w(seed.1)] }
    }
}

/// An Xorshift128[1] random number generator.
///
/// The Xorshift128 algorithm is not suitable for cryptographic purposes
/// but is very fast. If you do not know for sure that it fits your
/// requirements, use a more secure one such as `IsaacRng` or `OsRng`.
/// This variant uses 32bit arithmetic and is appropriated for 32bit architectures.
///
/// [1]: Marsaglia, George (July 2003). ["Xorshift
/// RNGs"](http://www.jstatsoft.org/v08/i14/paper). *Journal of
/// Statistical Software*. Vol. 8 (Issue 14).
#[derive(Copy, Clone)]
pub struct XorShiftRng {
    x: w32,
    y: w32,
    z: w32,
    w: w32,
}

impl XorShiftRng {
    /// Creates a new XorShiftRng instance which is not seeded.
    ///
    /// The initial values of this RNG are constants, so all generators created
    /// by this function will yield the same stream of random numbers. It is
    /// highly recommended that this is created through `SeedableRng` instead of
    /// this function
    pub fn new_unseeded() -> XorShiftRng {
        XorShiftRng {
            x: w(0x193a6754),
            y: w(0xa8a7d469),
            z: w(0x97830e05),
            w: w(0x113ba7bb),
        }
    }
}

impl Rng for XorShiftRng {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        let x = self.x;
        let t = x ^ (x << 11);
        self.x = self.y;
        self.y = self.z;
        self.z = self.w;
        let w_ = self.w;
        self.w = w_ ^ (w_ >> 19) ^ (t ^ (t >> 8));
        self.w.0
    }
}

impl SeedableRng<[u32; 4]> for XorShiftRng {
    /// Reseed an XorShiftRng. This will panic if `seed` is entirely 0.
    fn reseed(&mut self, seed: [u32; 4]) {
        assert!(seed != [0, 0, 0, 0],
                "XorShiftRng.reseed called with an all zero seed.");

        self.x = w(seed[0]);
        self.y = w(seed[1]);
        self.z = w(seed[2]);
        self.w = w(seed[3]);
    }

    /// Create a new XorShiftRng. This will panic if `seed` is entirely 0.
    fn from_seed(seed: [u32; 4]) -> XorShiftRng {
        assert!(seed != [0, 0, 0, 0],
                "XorShiftRng::from_seed called with an all zero seed.");

        XorShiftRng {
            x: w(seed[0]),
            y: w(seed[1]),
            z: w(seed[2]),
            w: w(seed[3]),
        }
    }
}

impl Rand for XorShiftRng {
    fn rand<R: Rng>(rng: &mut R) -> XorShiftRng {
        let mut tuple: (u32, u32, u32, u32) = rng.gen();
        while tuple == (0, 0, 0, 0) {
            tuple = rng.gen();
        }
        let (x, y, z, w_) = tuple;
        XorShiftRng { x: w(x), y: w(y), z: w(z), w: w(w_) }
    }
}

#[cfg(test)]
mod tests {
    use SeedableRng;
    use super::{XorShiftRng, XorShiftPlusRng};

    #[test]
    #[should_panic]
    fn test_xorshift64_zero_seed() {
        let _: XorShiftRng = SeedableRng::from_seed([0, 0, 0, 0]);
    }

    #[test]
    #[should_panic]
    fn test_xorshift128p_zero_seed() {
        let _: XorShiftPlusRng = SeedableRng::from_seed([0, 0]);
    }

    #[test]
    fn test_xorshift64_non_zero_seed() {
        let _: XorShiftRng = SeedableRng::from_seed([1, 1, 0, 0]);
    }

    #[test]
    fn test_xorshift128p_non_zero_seed() {
        let _: XorShiftPlusRng = SeedableRng::from_seed([1, 0]);
    }
}