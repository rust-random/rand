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
//! `SeedFromRng` and `SeedableRng` are extension traits for construction and
//! reseeding.
//! 
//! `Error` is provided for error-handling. It is safe to use in `no_std`
//! environments.
//! 
//! The `impls` sub-module includes a few small functions to assist
//! implementation of `Rng`. Since this module is only of interest to `Rng`
//! implementors, it is not re-exported from `rand`.

#![doc(html_logo_url = "https://www.rust-lang.org/logos/rust-logo-128x128-blk.png",
       html_favicon_url = "https://www.rust-lang.org/favicon.ico",
       html_root_url = "https://docs.rs/rand/0.3")]

#![deny(missing_debug_implementations)]

#![cfg_attr(not(feature="std"), no_std)]
#![cfg_attr(feature = "i128_support", feature(i128_type))]

// We need to use several items from "core" for no_std support.
#[cfg(feature="std")]
extern crate core;

#[cfg(feature="std")]
use std::error::Error as stdError;

use core::fmt;

pub mod impls;


/// A random number generator (not necessarily suitable for cryptography).
/// 
/// "Random" number generators can be categorised multiple ways:
/// 
/// *   *True* and *apparent* random number generators: *true* generators must
///     depend on some phenomenon which is actually random, such as atomic decay
///     or photon polarisation (note: bias may still be present, and it is
///     possible that these phenomena are in fact dependent on other unseen
///     parameters), while *apparent* random numbers are merely unpredictable.
/// *   *Algorithmic* and *external* generators: *algorithmic generators* can
///     never produce *true random numbers* but can still yield hard-to-predict
///     output. External generators may or may not use *true random sources*.
///     
///     *Algorithmic generators* are also known as *psuedo-random number
///     generators* or *PRNGs*.
///     
///     *Algorithmic* generators are necessarily deterministic: if two
///     generators using the same algorithm are initialised with the same seed,
///     they will necessarily produce the same output. PRNGs should normally
///     implement the `SeedableRng` trait, allowing this. To be reproducible
///     across platforms, conversion of output from one type to another should
///     pay special attention to endianness (we generally choose LE, e.g.
///     `fn next_u32(&mut self) -> u32 { self.next_u64() as u32 }`).
/// *   *Cryptographically secure*, *trivially predictable*, and various states
///     in between: if, after observing some output from an algorithmic
///     generator future output of the generator can be predicted, then it is
///     insecure.
///     
///     Note that all algorithmic generators eventually cycle,
///     returning to previous internal state and repeating all output, but in
///     good generators the period is so long that it is never reached (e.g. our
///     implementation of ChaCha would produce 2^134 bytes of output before
///     cycling, although cycles are not always so long). Predictability may not
///     be a problem for games, simulations and some randomised algorithms,
///     but unpredictability is essential in cryptography.
/// 
/// The `Rng` trait can be used for all the above types of generators. If using
/// random numbers for cryptography prefer to use numbers pulled from the OS
/// directly (`OsRng`) or at least use a generator implementing `CryptoRng`.
/// For applications where performance is important and unpredictability is
/// less critical but still somewhat important (e.g. to prevent a DoS attack),
/// one may prefer to use a `CryptoRng` generator or may consider other "hard
/// to predict" but not cryptographically proven generators.
/// 
/// PRNGs are usually infallible, while external generators may fail. Since
/// errors are rare and may be hard for the user to handle, most of the output
/// functions do not return a `Result`; byte output can however be retrieved
/// with `try_fill` which allows for the usual error handling. If the random
/// source implements other output functions in terms of `try_fill` (see
/// `impls::fill_via_try_fill`), then some errors will be handled implicitly,
/// so long as not too many retries are needed (specifically: `NotReady` is
/// handled by waiting up to 1 minute, and `Transient` is handled by retrying
/// a few times). In some applications it may make sense to ensure your entropy
/// source (e.g. `OsRng`) is ready by calling `try_fill` explicitly before
/// using any of the other output functions.
pub trait Rng {
    /// Return the next random u32.
    fn next_u32(&mut self) -> u32;

    /// Return the next random u64.
    fn next_u64(&mut self) -> u64;

    /// Return the next random u128.
    #[cfg(feature = "i128_support")]
    fn next_u128(&mut self) -> u128;

    /// Fill `dest` entirely with random data.
    ///
    /// This method does *not* have any requirement on how much of the
    /// generated random number stream is consumed; e.g. `fill_bytes_via_u64`
    /// implementation uses `next_u64` thus consuming 8 bytes even when only
    /// 1 is required. A different implementation might use `next_u32` and
    /// only consume 4 bytes; *however* any change affecting *reproducibility*
    /// of output must be considered a breaking change.
    fn fill_bytes(&mut self, dest: &mut [u8]);

    /// Fill `dest` entirely with random data.
    ///
    /// If a RNG can encounter an error, this is the only method that reports
    /// it. The other methods either handle the error, or panic.
    ///
    /// This method does *not* have any requirement on how much of the
    /// generated random number stream is consumed; e.g. `try_fill_via_u64`
    /// implementation uses `next_u64` thus consuming 8 bytes even when only
    /// 1 is required. A different implementation might use `next_u32` and
    /// only consume 4 bytes; *however* any change affecting *reproducibility*
    /// of output must be considered a breaking change.
    fn try_fill(&mut self, dest: &mut [u8]) -> Result<(), Error>;
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
pub trait CryptoRng: Rng {}


impl<'a, R: Rng+?Sized> Rng for &'a mut R {
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

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        (**self).fill_bytes(dest)
    }

    fn try_fill(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        (**self).try_fill(dest)
    }
}

#[cfg(feature="std")]
impl<R: Rng+?Sized> Rng for Box<R> {
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

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        (**self).fill_bytes(dest)
    }

    fn try_fill(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        (**self).try_fill(dest)
    }
}


/// Support mechanism for creating random number generators seeded by other
/// generators. All PRNGs should support this to enable `NewSeeded` support,
/// which should be the preferred way of creating randomly-seeded generators.
/// 
/// There are two subtle differences between `SeedFromRng::from_rng` and
/// `SeedableRng::from_seed` (beyond the obvious): first, that `from_rng` has
/// no reproducibility requirement, and second, that `from_rng` may directly
/// fill internal states larger than `SeedableRng::Seed`, where `from_seed` may
/// need some extra step to expand the input.
pub trait SeedFromRng: Sized {
    /// Creates a new instance, seeded from another `Rng`.
    /// 
    /// Seeding from a cryptographic generator should be fine. On the other
    /// hand, seeding a simple numerical generator from another of the same
    /// type sometimes has serious side effects such as effectively cloning the
    /// generator.
    fn from_rng<R: Rng>(rng: R) -> Result<Self, Error>;
}

/// A random number generator that can be explicitly seeded to produce
/// the same stream of randomness multiple times (i.e. is reproducible).
/// 
/// Note: this should only be implemented by reproducible generators (i.e.
/// where the algorithm is fixed and results should be the same across
/// platforms). This should not be implemented by wrapper types which choose
/// the underlying implementation based on platform, or which may change the
/// algorithm used in the future. This is to ensure that manual seeding of PRNGs
/// actually does yield reproducible results.
pub trait SeedableRng: Sized {
    /// Seed type.
    /// 
    /// TODO: restrict to `[u8; N]` where N in 8, 16, 32
    type Seed;
    
    /// Create a new PRNG using the given seed.
    /// 
    /// Each PRNG should implement this.
    /// 
    /// Reproducibility is required; that is, a fixed PRNG seeded using this
    /// function with a fixed seed should produce the same sequence of output
    /// today, and in the future. PRNGs not able to satisfy this should make
    /// clear notes in their documentation or not implement `SeedableRng` at
    /// all. It is however not required that this function yield the same state
    /// as a reference implementation of the PRNG given equivalent seed; if
    /// necessary another constructor should be used.
    /// 
    /// It may be expected that bits in the seed are well distributed, i.e. that
    /// values like 0, 1 and (size - 1) are unlikely. Users with poorly
    /// distributed input should use `from_hashable`.
    fn from_seed(seed: Self::Seed) -> Self;
}


/// Error kind which can be matched over.
#[derive(PartialEq, Eq, Debug, Copy, Clone)]
pub enum ErrorKind {
    /// Permanent failure: likely not recoverable without user action.
    Unavailable,
    /// Temporary failure: recommended to retry a few times, but may also be
    /// irrecoverable.
    Transient,
    /// Not ready yet: recommended to try again a little later.
    NotReady,
    /// Uncategorised error
    Other,
    #[doc(hidden)]
    __Nonexhaustive,
}

impl ErrorKind {
    /// True if this kind of error may resolve itself on retry.
    /// 
    /// See also `should_wait()`.
    pub fn should_retry(self) -> bool {
        match self {
            ErrorKind::Transient | ErrorKind::NotReady => true,
            _ => false,
        }
    }
    
    /// True if we should retry but wait before retrying
    /// 
    /// This implies `should_retry()` is true.
    pub fn should_wait(self) -> bool {
        self == ErrorKind::NotReady
    }
    
    /// A description of this error kind
    pub fn description(self) -> &'static str {
        match self {
            ErrorKind::Unavailable => "permanent failure or unavailable",
            ErrorKind::Transient => "transient failure",
            ErrorKind::NotReady => "not ready yet",
            ErrorKind::Other => "uncategorised",
            ErrorKind::__Nonexhaustive => unreachable!(),
        }
    }
}

/// Error type of random number generators
/// 
/// This embeds an `ErrorKind` which can be matched over, a *message* to tell
/// users what happened, and optionally a *cause* (which allows chaining back
/// to the original error).
/// 
/// The cause is omitted in `no_std` mode (see `Error::new` for details).
#[derive(Debug)]
pub struct Error {
    /// Error kind. This enum is included to aid handling of errors.
    pub kind: ErrorKind,
    msg: &'static str,
    #[cfg(feature="std")]
    cause: Option<Box<stdError + Send + Sync>>,
}

impl Error {
    /// Create a new instance, with specified kind and a message.
    pub fn new(kind: ErrorKind, msg: &'static str) -> Self {
        #[cfg(feature="std")] {
            Self { kind, msg, cause: None }
        }
        #[cfg(not(feature="std"))] {
            Self { kind, msg }
        }
    }
    /// Create a new instance, with specified kind, message, and a
    /// chained cause.
    /// 
    /// Note: `stdError` is an alias for `std::error::Error`.
    /// 
    /// If not targetting `std` (i.e. `no_std`), this function is replaced by
    /// another with the same prototype, except that there are no bounds on the
    /// type `E` (because both `Box` and `stdError` are unavailable), and the
    /// `cause` is ignored.
    #[cfg(feature="std")]
    pub fn with_cause<E>(kind: ErrorKind, msg: &'static str, cause: E) -> Self
        where E: Into<Box<stdError + Send + Sync>>
    {
        Self { kind, msg, cause: Some(cause.into()) }
    }
    /// Create a new instance, with specified kind, message, and a
    /// chained cause.
    /// 
    /// In `no_std` mode the *cause* is ignored.
    #[cfg(not(feature="std"))]
    pub fn with_cause<E>(kind: ErrorKind, msg: &'static str, _cause: E) -> Self {
        Self { kind, msg }
    }
    
    /// Get the error message
    pub fn msg(&self) -> &'static str {
        self.msg
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "RNG error [{}]: {}", self.kind.description(), self.msg())
    }
}

#[cfg(feature="std")]
impl stdError for Error {
    fn description(&self) -> &str {
        self.msg
    }

    fn cause(&self) -> Option<&stdError> {
        self.cause.as_ref().map(|e| e.as_ref() as &stdError)
    }
}

/// Little-Endian utilities
/// 
/// Little-Endian order has been chosen for internal usage; this makes some
/// useful functions available.
pub mod le {
    use core::slice;
    
    /// Helper function to turn a slice into an array reference
    
    /// Read a `u32` from a byte sequence, in litte-endian order
    /// 
    /// Consider usage with the `arrayref` crate.
    pub fn read_u32(bytes: &[u8; 4]) -> u32 {
        unsafe{ *(bytes as *const [u8; 4] as *const u32) }.to_le()
    }
    
    /// Read a `u64` from a byte sequence, in litte-endian order
    /// 
    /// Consider usage with the `arrayref` crate.
    pub fn read_u64(bytes: &[u8; 8]) -> u64 {
        unsafe{ *(bytes as *const [u8; 8] as *const u64) }.to_le()
    }
    
    /// Convert a byte slice to a `u32` slice and mutate endianness in-place
    pub fn convert_slice_32(bytes: &mut [u8]) -> &mut [u32] {
        assert_eq!(bytes.len() % 4, 0);
        let l = bytes.len() / 4;
        let p = bytes.as_ptr() as *mut u8 as *mut u32;
        let s = unsafe{ slice::from_raw_parts_mut(p, l) };
        for i in s.iter_mut() {
            *i = (*i).to_le();
        }
        s
    }
    
    /// Convert a byte slice to a `u64` slice and mutate endianness in-place
    pub fn convert_slice_64(bytes: &mut [u8]) -> &mut [u64] {
        assert_eq!(bytes.len() % 8, 0);
        let l = bytes.len() / 8;
        let p = bytes.as_ptr() as *mut u8 as *mut u64;
        let s = unsafe{ slice::from_raw_parts_mut(p, l) };
        for i in s.iter_mut() {
            *i = (*i).to_le();
        }
        s
    }
    
    #[cfg(test)]
    mod tests {
        use super::*;
        #[test]
        
        fn test_read() {
            assert_eq!(read_u32(&[1, 2, 3, 4]), 0x04030201);
            assert_eq!(read_u64(&[1, 2, 3, 4, 5, 6, 7, 8]), 0x0807060504030201);
            
            {
                let mut bytes = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
                let slice = convert_slice_32(&mut bytes[..]);
                assert_eq!(slice[0], 0x04030201);
                assert_eq!(slice[3], 0x100F0E0D);
            }
            {
                let mut bytes = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
                let slice = convert_slice_64(&mut bytes[..]);
                assert_eq!(slice[0], 0x0807060504030201);
                assert_eq!(slice[1], 0x100F0E0D0C0B0A09);
            }
        }
    }
}
