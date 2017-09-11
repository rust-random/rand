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
use {Rng, FromRng, SeedableRng};

#[cfg(target_pointer_width = "32")]
#[derive(Copy)]
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
pub struct IsaacWordRng(super::isaac::IsaacRng);

#[cfg(target_pointer_width = "64")]
#[derive(Copy)]
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
pub struct IsaacWordRng(super::isaac64::Isaac64Rng);

impl Clone for IsaacWordRng {
    fn clone(&self) -> IsaacWordRng {
        *self
    }
}

impl Rng for IsaacWordRng {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        self.0.next_u32()
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        self.0.next_u64()
    }
}

impl FromRng for IsaacWordRng {
    #[cfg(target_pointer_width = "32")]
    fn from_rng<R: Rng+?Sized>(other: &mut R) -> IsaacWordRng {
        IsaacWordRng(super::isaac::IsaacRng::from_rng(other))
    }

    #[cfg(target_pointer_width = "64")]
    fn from_rng<R: Rng+?Sized>(other: &mut R) -> IsaacWordRng {
        IsaacWordRng(super::isaac64::Isaac64Rng::from_rng(other))
    }
}

#[cfg(target_pointer_width = "32")]
impl<'a> SeedableRng<&'a [u32]> for IsaacWordRng {
    fn reseed(&mut self, seed: &'a [u32]) {
        self.0.reseed(seed)
    }

    /// Create an ISAAC random number generator with a seed. This can
    /// be any length, although the maximum number of elements used is
    /// 256 and any more will be silently ignored. A generator
    /// constructed with a given seed will generate the same sequence
    /// of values as all other generators constructed with that seed.
    fn from_seed(seed: &'a [u32]) -> IsaacWordRng {
        IsaacWordRng(super::isaac::IsaacRng::from_seed(seed))
    }
}

#[cfg(target_pointer_width = "64")]
impl<'a> SeedableRng<&'a [u64]> for IsaacWordRng {
    fn reseed(&mut self, seed: &'a [u64]) {
        self.0.reseed(seed)
    }

    /// Create an ISAAC random number generator with a seed. This can
    /// be any length, although the maximum number of elements used is
    /// 256 and any more will be silently ignored. A generator
    /// constructed with a given seed will generate the same sequence
    /// of values as all other generators constructed with that seed.
    fn from_seed(seed: &'a [u64]) -> IsaacWordRng {
        IsaacWordRng(super::isaac64::Isaac64Rng::from_seed(seed))
    }
}

impl fmt::Debug for IsaacWordRng {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "IsaacWordRng {{}}")
    }
}
