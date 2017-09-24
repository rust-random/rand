// Copyright 2013-2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Mock RNG implementations
//! 
//! TODO: should this be behind a feature flag? Problem is that Cargo won't
//! simply use a dependency with a feature flag for tests and without for normal
//! build (i.e. `rand` couldn't use the mock feature only for tests).
//! Instead maybe this should be yet another crate? Or just leave it here?

use core::num::Wrapping as w;
use {Rng, SeedableRng, impls, Result};

/// A simple implementation of `Rng`, purely for testing.
/// Returns an arithmetic sequence (i.e. adds a constant each step).
/// 
/// ```rust
/// use rand_core::Rng;
/// use rand_core::mock::MockAddRng;
/// 
/// let mut my_rng = MockAddRng::new(2u32, 1u32);
/// assert_eq!(my_rng.next_u32(), 2u32);
/// assert_eq!(my_rng.next_u64(), 3u64 + (4u64 << 32));
/// ```
#[derive(Debug)]
pub struct MockAddRng<T> {
    v: w<T>,
    a: w<T>,
}

impl<T> MockAddRng<T> {
    /// Create a `MockAddRng`, yielding an arithmetic sequence starting with
    /// `v` and incremented by `a` each time.
    pub fn new(v: T, a: T) -> Self {
        MockAddRng { v: w(v), a: w(a) }
    }
}

impl Rng for MockAddRng<u32> {
    fn next_u32(&mut self) -> u32 {
        let result = self.v.0;
        self.v += self.a;
        result
    }
    fn next_u64(&mut self) -> u64 {
        impls::next_u64_via_u32(self)
    }
    #[cfg(feature = "i128_support")]
    fn next_u128(&mut self) -> u128 {
        impls::next_u128_via_u64(self)
    }
    
    fn try_fill(&mut self, dest: &mut [u8]) -> Result<()> {
        impls::try_fill_via_u32(self, dest)
    }
}

impl Rng for MockAddRng<u64> {
    fn next_u32(&mut self) -> u32 {
        self.next_u64() as u32
    }
    fn next_u64(&mut self) -> u64 {
        let result = self.v.0;
        self.v += self.a;
        result
    }
    #[cfg(feature = "i128_support")]
    fn next_u128(&mut self) -> u128 {
        impls::next_u128_via_u64(self)
    }
    
    fn try_fill(&mut self, dest: &mut [u8]) -> Result<()> {
        impls::try_fill_via_u32(self, dest)
    }
}

impl<T> SeedableRng<T> for MockAddRng<T> where
        MockAddRng<T>: Rng,
        T: From<u8>,    // for 1.into()
{
    fn from_seed(seed: T) -> Self {
        MockAddRng::new(seed, 1.into())
    }
}
