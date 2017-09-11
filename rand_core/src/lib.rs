// Copyright 2013-2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Random number generation traits
//! 
//! This crate is mainly of interest to crates publishing implementations of
//! `Rng`. Other users are encouraged to use the
//! [rand crate](https://crates.io/crates/rand) instead.
//!
//! `Rng` is the core trait implemented by algorithmic pseudo-random number
//! generators and external random-number sources.
//! 
//! `SeedFromRng` and `SeedableRng` are extension traits.
//! 
//! `Error` and `Result` are provided for error-handling. They are safe to use
//! in `no_std` environments.

#![doc(html_logo_url = "https://www.rust-lang.org/logos/rust-logo-128x128-blk.png",
       html_favicon_url = "https://www.rust-lang.org/favicon.ico",
       html_root_url = "https://docs.rs/rand/0.3")]

#![deny(missing_debug_implementations)]

#![cfg_attr(not(feature="std"), no_std)]
#![cfg_attr(feature = "i128_support", feature(i128_type, i128))]

// We need to use several items from "core" for no_std support.
#[cfg(feature="std")]
extern crate core;


/// A random number generator.
/// 
/// There are two classes of generators: *algorithmic* generators, also called
/// PRNGs (Pseudo-Random Number Generators) and *external* generators.
/// 
/// Another classification for generators is those that are cryptographically
/// secure (CSPRNGs) and those that are not. CSPRNGs should satisfy two
/// additional properties: (1) given the first *k* bits of an algorithm's output
/// sequence, it should not be possible using polynomial-time algorithms to
/// predict the next bit with probability significantly greater than 50%, and
/// (2) if a CSPRNG's state is revealed, it should not be
/// computationally-feasible to reconstruct output prior to this.
/// 
/// PRNGs are expected to be reproducible: that is, when a fixed algorithm is
/// seeded with a fixed value, then calling *any* sequence of the `Rng`'s
/// functions should produce a fixed sequence of values, and produce the *same*
/// sequence of values on every platform. This necessitates that a PRNG have
/// fixed endianness.
/// 
/// All default implementations use little-endian code (e.g. to construct a
/// `u64` from two `u32` numbers, the first is the low part). To implement
/// `next_u32` in terms of `next_u64`, one should write `self.next_u64() as u32`
/// which takes the least-significant half (LE order).
/// 
/// PRNGs are normally infallible, while external generators may fail. PRNGs
/// however have a finite period, and may emit an error rather than loop (this
/// is important for CSPRNGs which could conceivably cycle, but non-crypto
/// generators should simply cycle; in many cases the period is so long that
/// consuming all available values would be inconceivable).
/// 
/// TODO: details on error handling are under discussion; for now implementations
/// may panic.
pub trait Rng {
    /// Return the next random u32.
    fn next_u32(&mut self) -> u32;

    /// Return the next random u64.
    ///
    /// By default this is implemented in terms of `next_u32` in LE order. An
    /// implementation of this trait must provide at least one of
    /// these two methods. Similarly to `next_u32`, this rarely needs
    /// to be called directly, prefer `r.gen()` to `r.next_u64()`.
    fn next_u64(&mut self) -> u64 {
        // Use LE; we explicitly generate one value before the next.
        let x = self.next_u32() as u64;
        let y = self.next_u32() as u64;
        (y << 32) | x
    }

    #[cfg(feature = "i128_support")]
    /// Return the next random u128.
    /// 
    /// By default this is implemented in terms of `next_u64` in LE order.
    fn next_u128(&mut self) -> u128 {
        // Use LE; we explicitly generate one value before the next.
        let x = self.next_u64() as u128;
        let y = self.next_u64() as u128;
        (y << 64) | x
    }
    
    /// Fill `dest` entirely with random data.
    ///
    /// This has a default implementation in terms of `next_u64` in LE order,
    /// but should be overridden by implementations that
    /// offer a more efficient solution than just calling `next_u64`
    /// repeatedly.
    ///
    /// This method does *not* have any requirement on how much of the
    /// generated random number stream is consumed; e.g. the default
    /// implementation uses `next_u64` thus consuming 8 bytes even when only
    /// 1 is required. A different implementation might use `next_u32` and
    /// only consume 4 bytes; *however* any change affecting *reproducibility*
    /// of output must be considered a breaking change.
    fn try_fill(&mut self, dest: &mut [u8]) -> Result<()> {
        use core::intrinsics::transmute;
        
        let mut left = dest;
        while left.len() >= 8 {
            let (l, r) = {left}.split_at_mut(8);
            left = r;
            let chunk: [u8; 8] = unsafe {
                transmute(self.next_u64().to_le())
            };
            l.copy_from_slice(&chunk);
        }
        let n = left.len();
        if n > 0 {
            let chunk: [u8; 8] = unsafe {
                transmute(self.next_u64().to_le())
            };
            left.copy_from_slice(&chunk[..n]);
        }
        Ok(())
    }
}

#[cfg(feature="std")]
impl<R> Rng for Box<R> where R: Rng+?Sized {
    fn next_u32(&mut self) -> u32 {
        (**self).next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        (**self).next_u64()
    }

    #[cfg(feature = "i128_support")]
    fn next_u128(&mut self) -> u128 {
        (**self).next_u128()
    }

    fn try_fill(&mut self, dest: &mut [u8]) -> Result<()> {
        (**self).try_fill(dest)
    }
}


/// Support mechanism for creating random number generators seeded by other
/// generators. All PRNGs should support this to enable `NewSeeded` support.
/// 
/// TODO: should this use `Distribution` instead? That would require moving
/// that trait and a distribution type to this crate.
/// TODO: should the source requirement be changed, e.g. to `CryptoRng`?
/// Note: this is distinct from `SeedableRng` because it is generic over the
/// RNG type (achieving the same with `SeedableRng` would require dynamic
/// dispatch: `SeedableRng<&mut Rng>`).
pub trait SeedFromRng: Sized {
    /// Creates a new instance, seeded from another `Rng`.
    /// 
    /// Seeding from a cryptographic generator should be fine. On the other
    /// hand, seeding a simple numerical generator from another of the same
    /// type sometimes has serious side effects such as effectively cloning the
    /// generator.
    fn from_rng<R: Rng+?Sized>(rng: &mut R) -> Result<Self>;
}


/// A random number generator that can be explicitly seeded to produce
/// the same stream of randomness multiple times.
pub trait SeedableRng<Seed>: Rng {
    /// Reseed an RNG with the given seed.
    /// 
    /// The type of `Seed` is specified by the implementation (implementation
    /// for multiple seed types is possible).
    fn reseed(&mut self, Seed);

    /// Create a new RNG with the given seed.
    /// 
    /// The type of `Seed` is specified by the implementation (implementation
    /// for multiple seed types is possible).
    fn from_seed(seed: Seed) -> Self;
}


/// Error type for cryptographic generators. Only operating system and hardware
/// generators should be able to fail. In such cases there is little that can
/// be done besides try again later.
#[derive(Debug)]
pub struct Error;

#[cfg(feature="std")]
impl From<::std::io::Error> for Error {
    fn from(_: ::std::io::Error) -> Error {
        Error
    }
}

/// Result type (convenience type-def)
pub type Result<T> = ::std::result::Result<T, Error>;
