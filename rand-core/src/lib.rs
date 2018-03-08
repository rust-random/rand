// Copyright 2017-2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Random number generation traits
//! 
//! This crate is mainly of interest to crates publishing implementations of
//! `RngCore`. Other users are encouraged to use the
//! [rand crate](https://crates.io/crates/rand) instead.
//!
//! `RngCore` is the core trait implemented by algorithmic pseudo-random number
//! generators and external random-number sources.
//! 
//! `SeedableRng` is an extension trait for construction from fixed seeds and
//! other random number generators.
//! 
//! `Error` is provided for error-handling. It is safe to use in `no_std`
//! environments.
//! 
//! The `impls` and `le` sub-modules include a few small functions to assist
//! implementation of `RngCore`. Since this module is only of interest to
//! `RngCore` implementors, it is not re-exported from `rand`.

#![doc(html_logo_url = "https://www.rust-lang.org/logos/rust-logo-128x128-blk.png",
       html_favicon_url = "https://www.rust-lang.org/favicon.ico",
       html_root_url = "https://docs.rs/rand-core/0.1")]

#![deny(missing_debug_implementations)]

#![cfg_attr(not(feature="std"), no_std)]
#![cfg_attr(all(feature="alloc", not(feature="std")), feature(alloc))]

#[cfg(feature="std")] extern crate core;
#[cfg(all(feature = "alloc", not(feature="std")))] extern crate alloc;


use core::default::Default;
use core::convert::AsMut;

#[cfg(all(feature="alloc", not(feature="std")))] use alloc::boxed::Box;

pub use error::{ErrorKind, Error};


mod error;
pub mod impls;
pub mod le;


/// The core of a random number generator.
/// 
/// This trait encapsulates the low-level functionality common to all
/// generators, and is the "back end", to be implemented by generators.
/// End users should normally use [`Rng`] instead.
/// 
/// Unlike [`Rng`], this trait is object-safe. To use a type-erased [`Rng`] —
/// i.e. dynamic dispatch — this trait must be used (also import [`Rng`] to
/// use its generic functions):
/// 
/// ```
/// use rand_core::RngCore;
/// 
/// fn use_rng(mut rng: &mut RngCore) -> u32 {
///     rng.next_u32()
/// }
/// 
/// // or:
/// fn use_any_rng<R: RngCore>(rng: &mut R) -> u32 {
///     rng.next_u32()
/// }
/// ```
/// 
/// Several extension traits exist:
/// 
/// *   [`Rng`] provides high-level functionality using generic functions
/// *   [`SeedableRng`] is another low-level trait to be implemented by PRNGs
///     (algorithmic RNGs), concerning creation and seeding
/// *   [`NewRng`] is a high-level trait providing a `new()` function, allowing
///     easy construction of freshly-seeded PRNGs
/// 
/// [`Rng`]: https://docs.rs/rand/0.5/rand/trait.Rng.html
/// [`SeedableRng`]: trait.SeedableRng.html
/// [`NewRng`]: https://docs.rs/rand/0.5/rand/trait.NewRng.html
pub trait RngCore {
    /// Return the next random `u32`.
    ///
    /// Implementations of this trait must implement at least one of
    /// `next_u32`, `next_u64` and `fill_bytes` directly. In the case this
    /// function is not implemented directly, it can be implemented using
    /// `self.next_u64() as u32` or via `fill_bytes`.
    fn next_u32(&mut self) -> u32;

    /// Return the next random `u64`.
    ///
    /// Implementations of this trait must implement at least one of
    /// `next_u32`, `next_u64` and `fill_bytes` directly. In the case this
    /// function is not implemented directly, the default implementation will
    /// generate values via `next_u32` in little-endian fashion, or this
    /// function can be implemented via `fill_bytes`.
    ///
    /// Types wrapping an inner RNG must not use the default implementation,
    /// since the inner RNG's implementation may produce different values.
    fn next_u64(&mut self) -> u64 {
        impls::next_u64_via_u32(self)
    }

    /// Fill `dest` with random data.
    ///
    /// Implementations of this trait must implement at least one of
    /// `next_u32`, `next_u64` and `fill_bytes` directly. In the case this
    /// function is not implemented directly, the default implementation will
    /// generate values via `next_u64` in little-endian fashion.
    ///
    /// There is no requirement on how this method generates values relative to
    /// `next_u32` or `next_u64`; e.g. a `u64` cast to bytes is not required to
    /// have the same value as eight bytes filled via this function. There *is*
    /// a requirement of portability for reproducible generators which implies
    /// that any seedable generator must fix endianness when generating bytes.
    ///
    /// Types wrapping an inner RNG must not use the default implementation,
    /// since the inner RNG's implementation may produce different values.
    ///
    /// This method should guarantee that `dest` is entirely filled
    /// with new data, and may panic if this is impossible
    /// (e.g. reading past the end of a file that is being used as the
    /// source of randomness).
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        impls::fill_bytes_via_u64(self, dest)
    }

    /// Fill `dest` entirely with random data.
    ///
    /// This is the only method which allows an RNG to report errors while
    /// generating random data; other methods either handle the error
    /// internally or panic. This method is
    /// the intended way to use external (true) RNGs, like `OsRng`. Its main
    /// use-cases are to generate keys and to seed (infallible) PRNGs.
    /// 
    /// Other than error handling, this method is identical to [`fill_bytes`], and
    /// has a default implementation simply wrapping [`fill_bytes`].
    /// 
    /// [`fill_bytes`]: trait.RngCore.html#method.fill_bytes
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        Ok(self.fill_bytes(dest))
    }
}

/// A marker trait for an `Rng` which may be considered for use in
/// cryptography.
/// 
/// *Cryptographically secure generators*, also known as *CSPRNGs*, should
/// satisfy an additional properties over other generators: given the first
/// *k* bits of an algorithm's output
/// sequence, it should not be possible using polynomial-time algorithms to
/// predict the next bit with probability significantly greater than 50%.
/// 
/// Some generators may satisfy an additional property, however this is not
/// required: if the CSPRNG's state is revealed, it should not be
/// computationally-feasible to reconstruct output prior to this. Some other
/// generators allow backwards-computation and are consided *reversible*.
/// 
/// Note that this trait is provided for guidance only and cannot guarantee
/// suitability for cryptographic applications. In general it should only be
/// implemented for well-reviewed code implementing well-regarded algorithms.
/// 
/// Note also that use of a `CryptoRng` does not protect against other
/// weaknesses such as seeding from a weak entropy source or leaking state.
pub trait CryptoRng: RngCore {}

/// A random number generator that can be explicitly seeded.
///
/// This trait encapsulates the low-level functionality common to all
/// pseudo-random number generators (PRNGs, or algorithmic generators).
/// 
/// Normally users should use the [`NewRng`] extension trait, excepting when a
/// fixed seed must be used, in which case usage of [`SeedableRng::from_seed`]
/// is recommended.
/// 
/// [`NewRng`]: https://docs.rs/rand/0.5/rand/trait.NewRng.html
/// [`SeedableRng::from_seed`]: #tymethod.from_seed
pub trait SeedableRng: Sized {
    /// Seed type, which is restricted to types mutably-dereferencable as `u8`
    /// arrays (we recommend `[u8; N]` for some `N`).
    ///
    /// It is recommended to seed PRNGs with a seed of at least circa 100 bits,
    /// which means an array of `[u8; 12]` or greater to avoid picking RNGs with
    /// partially overlapping periods.
    ///
    /// For cryptographic RNG's a seed of 256 bits is recommended, `[u8; 32]`.
    type Seed: Sized + Default + AsMut<[u8]>;

    /// Create a new PRNG using the given seed.
    ///
    /// PRNG implementations are allowed to assume that bits in the seed are
    /// well distributed. That means usually that the number of one and zero
    /// bits are about equal, and values like 0, 1 and (size - 1) are unlikely.
    ///
    /// PRNG implementations are recommended to be reproducible. A PRNG seeded
    /// using this function with a fixed seed should produce the same sequence
    /// of output in the future and on different architectures (with for example
    /// different endianness).
    ///
    /// It is however not required that this function yield the same state as a
    /// reference implementation of the PRNG given equivalent seed; if necessary
    /// another constructor can be used.
    fn from_seed(seed: Self::Seed) -> Self;

    /// Create a new PRNG seeded from another `Rng`.
    ///
    /// This is the recommended way to initialize PRNGs with fresh entropy. The
    /// [`NewRng`] trait provides a convenient new method based on `from_rng`.
    /// 
    /// Usage of this method is not recommended when reproducibility is required
    /// since implementing PRNGs are not required to fix Endianness and are
    /// allowed to modify implementations in new releases.
    ///
    /// It is important to use a good source of randomness to initialize the
    /// PRNG. Cryptographic PRNG may be rendered insecure when seeded from a
    /// non-cryptographic PRNG or with insufficient entropy.
    /// Many non-cryptographic PRNGs will show statistical bias in their first
    /// results if their seed numbers are small or if there is a simple pattern
    /// between them.
    ///
    /// Prefer to seed from a strong external entropy source like [`OsRng`] or
    /// from a cryptographic PRNG; if creating a new generator for cryptographic
    /// uses you *must* seed from a strong source.
    ///
    /// Seeding a small PRNG from another small PRNG is possible, but
    /// something to be careful with. An extreme example of how this can go
    /// wrong is seeding an [`XorShiftRng`] from another [`XorShiftRng`], which
    /// will effectively clone the generator. In general seeding from a
    /// generator which is hard to predict is probably okay.
    ///
    /// PRNG implementations are allowed to assume that a good RNG is provided
    /// for seeding, and that it is cryptographically secure when appropriate.
    /// 
    /// [`NewRng`]: https://docs.rs/rand/0.5/rand/trait.NewRng.html
    /// [`OsRng`]: https://docs.rs/rand/0.5/rand/os/struct.OsRng.html
    /// [`XorShiftRng`]: https://docs.rs/rand/0.5/rand/prng/xorshift/struct.XorShiftRng.html
    fn from_rng<R: RngCore>(rng: &mut R) -> Result<Self, Error> {
        let mut seed = Self::Seed::default();
        rng.try_fill_bytes(seed.as_mut())?;
        Ok(Self::from_seed(seed))
    }
}


impl<'a, R: RngCore + ?Sized> RngCore for &'a mut R {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        (**self).next_u32()
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        (**self).next_u64()
    }

    #[inline]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        (**self).fill_bytes(dest)
    }
    
    #[inline]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        (**self).try_fill_bytes(dest)
    }
}

#[cfg(any(feature="std", feature="alloc"))]
impl<R: RngCore + ?Sized> RngCore for Box<R> {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        (**self).next_u32()
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        (**self).next_u64()
    }

    #[inline]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        (**self).fill_bytes(dest)
    }
    
    #[inline]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        (**self).try_fill_bytes(dest)
    }
}
