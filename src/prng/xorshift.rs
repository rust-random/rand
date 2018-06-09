// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Xorshift generators

use core::num::Wrapping as w;
use core::{fmt, slice};
use rand_core::{RngCore, SeedableRng, Error, impls, le};

/// An Xorshift random number generator.
///
/// The Xorshift[^1] algorithm is not suitable for cryptographic purposes
/// but is very fast. If you do not know for sure that it fits your
/// requirements, use a more secure one such as `IsaacRng` or `OsRng`.
///
/// [^1]: Marsaglia, George (July 2003).
///       ["Xorshift RNGs"](https://www.jstatsoft.org/v08/i14/paper).
///       *Journal of Statistical Software*. Vol. 8 (Issue 14).
#[derive(Clone)]
#[cfg_attr(feature="serde1", derive(Serialize,Deserialize))]
pub struct XorShiftRng {
    x: w<u32>,
    y: w<u32>,
    z: w<u32>,
    w: w<u32>,
}

// Custom Debug implementation that does not expose the internal state
impl fmt::Debug for XorShiftRng {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "XorShiftRng {{}}")
    }
}

impl XorShiftRng {
    /// Creates a new XorShiftRng instance which is not seeded.
    ///
    /// The initial values of this RNG are constants, so all generators created
    /// by this function will yield the same stream of random numbers. It is
    /// highly recommended that this is created through `SeedableRng` instead of
    /// this function
    #[deprecated(since="0.5.0", note="use the FromEntropy or SeedableRng trait")]
    pub fn new_unseeded() -> XorShiftRng {
        XorShiftRng {
            x: w(0x193a6754),
            y: w(0xa8a7d469),
            z: w(0x97830e05),
            w: w(0x113ba7bb),
        }
    }
}

impl RngCore for XorShiftRng {
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

    #[inline]
    fn next_u64(&mut self) -> u64 {
        impls::next_u64_via_u32(self)
    }

    #[inline]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        impls::fill_bytes_via_next(self, dest)
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        Ok(self.fill_bytes(dest))
    }
}

impl SeedableRng for XorShiftRng {
    type Seed = [u8; 16];

    fn from_seed(seed: Self::Seed) -> Self {
        let mut seed_u32 = [0u32; 4];
        le::read_u32_into(&seed, &mut seed_u32);

        // Xorshift cannot be seeded with 0 and we cannot return an Error, but
        // also do not wish to panic (because a random seed can legitimately be
        // 0); our only option is therefore to use a preset value.
        if seed_u32.iter().all(|&x| x == 0) {
            seed_u32 = [0xBAD_5EED, 0xBAD_5EED, 0xBAD_5EED, 0xBAD_5EED];
        }

        XorShiftRng {
            x: w(seed_u32[0]),
            y: w(seed_u32[1]),
            z: w(seed_u32[2]),
            w: w(seed_u32[3]),
        }
    }

    fn from_rng<R: RngCore>(mut rng: R) -> Result<Self, Error> {
        let mut seed_u32 = [0u32; 4];
        loop {
            unsafe {
                let ptr = seed_u32.as_mut_ptr() as *mut u8;

                let slice = slice::from_raw_parts_mut(ptr, 4 * 4);
                rng.try_fill_bytes(slice)?;
            }
            if !seed_u32.iter().all(|&x| x == 0) { break; }
        }

        Ok(XorShiftRng {
            x: w(seed_u32[0]),
            y: w(seed_u32[1]),
            z: w(seed_u32[2]),
            w: w(seed_u32[3]),
        })
    }
}

#[cfg(test)]
mod tests {
    use {RngCore, SeedableRng};
    use super::XorShiftRng;

    #[test]
    fn test_xorshift_construction() {
        // Test that various construction techniques produce a working RNG.
        let seed = [1,2,3,4, 5,6,7,8, 9,10,11,12, 13,14,15,16];
        let mut rng1 = XorShiftRng::from_seed(seed);
        assert_eq!(rng1.next_u64(), 4325440999699518727);

        let _rng2 = XorShiftRng::from_rng(rng1).unwrap();
        // Note: we cannot test the state of _rng2 because from_rng does not
        // fix Endianness. This is allowed in the trait specification.
    }

    #[test]
    fn test_xorshift_true_values() {
        let seed = [16,15,14,13, 12,11,10,9, 8,7,6,5, 4,3,2,1];
        let mut rng = XorShiftRng::from_seed(seed);

        let mut results = [0u32; 9];
        for i in results.iter_mut() { *i = rng.next_u32(); }
        let expected: [u32; 9] = [
            2081028795, 620940381, 269070770, 16943764, 854422573, 29242889,
            1550291885, 1227154591, 271695242];
        assert_eq!(results, expected);

        let mut results = [0u64; 9];
        for i in results.iter_mut() { *i = rng.next_u64(); }
        let expected: [u64; 9] = [
            9247529084182843387, 8321512596129439293, 14104136531997710878,
            6848554330849612046, 343577296533772213, 17828467390962600268,
            9847333257685787782, 7717352744383350108, 1133407547287910111];
        assert_eq!(results, expected);

        let mut results = [0u8; 32];
        rng.fill_bytes(&mut results);
        let expected = [102, 57, 212, 16, 233, 130, 49, 183,
                        158, 187, 44, 203, 63, 149, 45, 17,
                        117, 129, 131, 160, 70, 121, 158, 155,
                        224, 209, 192, 53, 10, 62, 57, 72];
        assert_eq!(results, expected);
    }

    #[test]
    fn test_xorshift_zero_seed() {
        // Xorshift does not work with an all zero seed.
        // Assert it does not panic.
        let seed = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
        let mut rng = XorShiftRng::from_seed(seed);
        let a = rng.next_u64();
        let b = rng.next_u64();
        assert!(a != 0);
        assert!(b != a);
    }

    #[test]
    fn test_xorshift_clone() {
        let seed = [1,2,3,4, 5,5,7,8, 8,7,6,5, 4,3,2,1];
        let mut rng1 = XorShiftRng::from_seed(seed);
        let mut rng2 = rng1.clone();
        for _ in 0..16 {
            assert_eq!(rng1.next_u64(), rng2.next_u64());
        }
    }

    #[cfg(all(feature="serde1", feature="std"))]
    #[test]
    fn test_xorshift_serde() {
        use bincode;
        use std::io::{BufWriter, BufReader};

        let seed = [1,2,3,4, 5,6,7,8, 9,10,11,12, 13,14,15,16];
        let mut rng = XorShiftRng::from_seed(seed);

        let buf: Vec<u8> = Vec::new();
        let mut buf = BufWriter::new(buf);
        bincode::serialize_into(&mut buf, &rng).expect("Could not serialize");

        let buf = buf.into_inner().unwrap();
        let mut read = BufReader::new(&buf[..]);
        let mut deserialized: XorShiftRng = bincode::deserialize_from(&mut read).expect("Could not deserialize");

        assert_eq!(rng.x, deserialized.x);
        assert_eq!(rng.y, deserialized.y);
        assert_eq!(rng.z, deserialized.z);
        assert_eq!(rng.w, deserialized.w);

        for _ in 0..16 {
            assert_eq!(rng.next_u64(), deserialized.next_u64());
        }
    }
}
