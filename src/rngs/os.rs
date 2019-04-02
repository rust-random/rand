// Copyright 2019 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Interface to the random number generator of the operating system.

use getrandom::getrandom;
use rand_core::{CryptoRng, RngCore, Error, ErrorKind, impls};

/// A random number generator that retrieves randomness from from the
/// operating system.
///
/// This is a zero-sized struct. It can be freely constructed with `OsRng`.
/// 
/// The implementation is provided by the [getrandom] crate. Refer to
/// [getrandom] documentation for details.
///
/// [getrandom]: https://crates.io/crates/getrandom
#[derive(Clone, Copy, Debug)]
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
        
        getrandom(dest).map_err(|e|
            Error::with_cause(ErrorKind::Unavailable, "OsRng failed", e))
    }
}

#[test]
fn test_os_rng() {
    let x = OsRng.next_u64();
    let y = OsRng.next_u64();
    assert!(x != 0);
    assert!(x != y);
}
