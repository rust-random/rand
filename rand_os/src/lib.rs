// Copyright 2025 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! [`OsRng`] provider
//!
//! This crate may be used instead of (or as well as) [`rand`] to use [`OsRng`].
//! Both the [`OsRng`] provided by this crate and [`rand::rngs::OsRng`] are thin
//! wrappers over [getrandom].
//!
//! [getrandom]: https://crates.io/crates/getrandom
//! [`rand`]: https://docs.rs/rand/
//! [`rand::rngs::OsRng`]: https://docs.rs/rand/latest/rand/rngs/struct.OsRng.html

pub extern crate rand_core;
pub extern crate getrandom;

use rand_core::{TryCryptoRng, TryRngCore};

/// An interface over the operating-system's random data source
///
/// This is a zero-sized struct. It can be freely constructed with just `OsRng`.
///
/// The implementation is provided by the [getrandom] crate. Refer to
/// [getrandom] documentation for details.
///
/// # Usage example
/// ```
/// use rand_os::rand_core::TryRngCore;
/// use rand_os::OsRng;
///
/// let mut key = [0u8; 32];
/// OsRng.try_fill_bytes(&mut key).unwrap();
/// let random_u64 = OsRng.try_next_u64().unwrap();
/// ```
///
/// [getrandom]: https://crates.io/crates/getrandom
#[derive(Clone, Copy, Debug, Default)]
pub struct OsRng;

impl TryRngCore for OsRng {
    type Error = getrandom::Error;

    #[inline]
    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        getrandom::u32()
    }

    #[inline]
    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        getrandom::u64()
    }

    #[inline]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Self::Error> {
        getrandom::fill(dest)
    }
}

impl TryCryptoRng for OsRng {}

#[test]
fn test_os_rng() {
    let x = OsRng.try_next_u64().unwrap();
    let y = OsRng.try_next_u64().unwrap();
    assert!(x != 0);
    assert!(x != y);
}

#[test]
fn test_construction() {
    assert!(OsRng.try_next_u64().unwrap() != 0);
}
