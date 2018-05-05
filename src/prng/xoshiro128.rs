// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! XoShiro128 generator

use core::num::Wrapping as w;
use core::{fmt, slice};
use rand_core::{RngCore, SeedableRng, Error, impls, le};

#[inline(always)]
fn rotl(x: w<u64>, k: usize) -> w<u64> {
    (x << k)| (x >> (64 - k))
}

/// An XoroShiro256 random number generator.
pub struct XoShiro128 {
    s: [w<u64>; 2]
}

// Custom Debug implementation that does not expose the internal state
impl fmt::Debug for XoShiro128 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "XoShiro128 {{}}")
    }
}

impl RngCore for XoShiro128 {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        self.next_u64() as u32
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        let s0 = self.s[0];
        let mut s1 = self.s[1];
        let result = rotl(s0 * w(5), 7) * w(9);

        s1 ^= s0;
        self.s[0] = rotl(s0, 24) ^ s1 ^ (s1 << 16);
        self.s[1] = rotl(s1, 37);

        result.0
    }

    #[inline]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        impls::fill_bytes_via_next(self, dest)
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        Ok(self.fill_bytes(dest))
    }
}

impl SeedableRng for XoShiro128 {
    type Seed = [u8; 16];

    fn from_seed(seed: Self::Seed) -> Self {
        let mut seed_u64 = [0u64; 2];
        le::read_u64_into(&seed, &mut seed_u64);

        // XoShiro128 cannot be seeded with 0 and we cannot return an Error, but
        // also do not wish to panic (because a random seed can legitimately be
        // 0); our only option is therefore to use a preset value.
        if seed_u64.iter().all(|&x| x == 0) {
            seed_u64 = [0xBAD_5EED, 0xBAD_5EED];
        }

        XoShiro128 {
            s: [w(seed_u64[0]), w(seed_u64[0])]
        }
    }

    fn from_rng<R: RngCore>(mut rng: R) -> Result<Self, Error> {
        let mut seed_u64 = [0u64; 2];
        loop {
            unsafe {
                let ptr = seed_u64.as_mut_ptr() as *mut u8;

                let slice = slice::from_raw_parts_mut(ptr, 4 * 4);
                rng.try_fill_bytes(slice)?;
            }
            if !seed_u64.iter().all(|&x| x == 0) { break; }
        }

        Ok(XoShiro128 {
            s: [w(seed_u64[0]), w(seed_u64[0])]
        })
    }
}