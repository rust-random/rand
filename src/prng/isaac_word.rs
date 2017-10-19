// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The ISAAC random number generator.

use core::fmt;
use {Rng, SeedFromRng, Error};

#[cfg(target_pointer_width = "32")]
type WordRngType = super::isaac::IsaacRng;
#[cfg(target_pointer_width = "64")]
type WordRngType = super::isaac64::Isaac64Rng;

/// A random number generator that uses the ISAAC or ISAAC-64 algorithm,
/// depending on the pointer size of the target architecture.
///
/// In general a random number generator that internally uses the word size of
/// the target architecture is faster than one that doesn't. Choosing
/// `IsaacWordRng` is therefore often a better choice than `IsaacRng` or
/// `Isaac64Rng`. The others can be a good choice if reproducability across
/// different architectures is desired. `IsaacRng` can also be a better choice
/// if memory usage is an issue, as it uses 2kb of state instead of the 4kb
/// `Isaac64Rng` uses.
///
/// See for an explanation of the algorithm `IsaacRng` and `Isaac64Rng`.
#[derive(Copy)]
pub struct IsaacWordRng(WordRngType);

impl Clone for IsaacWordRng {
    fn clone(&self) -> IsaacWordRng {
        *self
    }
}

impl Rng for IsaacWordRng {
    fn next_u32(&mut self) -> u32 {
        self.0.next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        self.0.next_u64()
    }
    
    #[cfg(feature = "i128_support")]
    fn next_u128(&mut self) -> u128 {
        self.0.next_u128()
    }
    
    fn try_fill(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        self.0.try_fill(dest)
    }
}

impl SeedFromRng for IsaacWordRng {
    fn from_rng<R: Rng+?Sized>(other: &mut R) -> Result<Self, Error> {
        WordRngType::from_rng(other).map(|rng| IsaacWordRng(rng))
    }
}

impl fmt::Debug for IsaacWordRng {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "IsaacWordRng {{}}")
    }
}
