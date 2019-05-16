// Copyright 2018 Developers of the Rand project.
// Copyright 2013-2015 The Rust Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Interface to the random number generator of the operating system.
//!
//! # Blocking and error handling
//!
//! It is possible that when used during early boot the first call to `OsRng`
//! will block until the system's RNG is initialised. It is also possible
//! (though highly unlikely) for `OsRng` to fail on some platforms, most
//! likely due to system mis-configuration.
//!
//! After the first successful call, it is highly unlikely that failures or
//! significant delays will occur (although performance should be expected to
//! be much slower than a user-space PRNG).
//!
//! [getrandom]: https://crates.io/crates/getrandom
#![doc(html_logo_url = "https://www.rust-lang.org/logos/rust-logo-128x128-blk.png",
       html_favicon_url = "https://www.rust-lang.org/favicon.ico",
       html_root_url = "https://rust-random.github.io/rand/")]
#![deny(missing_docs)]
#![deny(missing_debug_implementations)]
#![doc(test(attr(allow(unused_variables), deny(warnings))))]

#![cfg_attr(feature = "stdweb", recursion_limit="128")]

#![no_std]  // but see getrandom crate

pub use rand_core;  // re-export

use getrandom::getrandom;
use rand_core::{CryptoRng, RngCore, Error, impls};

/// A random number generator that retrieves randomness from from the
/// operating system.
///
/// This is a zero-sized struct. It can be freely constructed with `OsRng`.
///
/// The implementation is provided by the [getrandom] crate. Refer to
/// [getrandom] documentation for details.
///
/// # Usage example
/// ```
/// use rand_os::{OsRng, rand_core::RngCore};
///
/// let mut key = [0u8; 16];
/// OsRng.fill_bytes(&mut key);
/// let random_u64 = OsRng.next_u64();
/// ```
///
/// [getrandom]: https://crates.io/crates/getrandom
#[derive(Clone, Copy, Debug, Default)]
pub struct OsRng;

impl OsRng {
    /// Create a new `OsRng`.
    #[deprecated(since="0.2.0", note="replace OsRng::new().unwrap() with just OsRng")]
    pub fn new() -> Result<OsRng, Error> {
        Ok(OsRng)
    }
}

impl CryptoRng for OsRng {}

impl RngCore for OsRng {
    fn next_u32(&mut self) -> u32 {
        impls::next_u32_via_fill(self)
    }

    fn next_u64(&mut self) -> u64 {
        impls::next_u64_via_fill(self)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        if let Err(e) = self.try_fill_bytes(dest) {
            panic!("Error: {}", e);
        }
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        // Some systems do not support reading 0 random bytes.
        // (And why waste a system call?)
        if dest.len() == 0 { return Ok(()); }
        
        getrandom(dest).map_err(|e| Error::with_cause("OsRng failed", e))
    }
}

#[test]
fn test_os_rng() {
    let x = OsRng.next_u64();
    let y = OsRng.next_u64();
    assert!(x != 0);
    assert!(x != y);
}

#[test]
fn test_construction() {
    let mut rng = OsRng::default();
    assert!(rng.next_u64() != 0);
}
