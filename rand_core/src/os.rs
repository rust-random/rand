// Copyright 2019 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Interface to the random number generator of the operating system.

use crate::{TryCryptoRng, TryRngCore};
use getrandom::getrandom;

/// A random number generator that retrieves randomness from the
/// operating system.
///
/// This is a zero-sized struct. It can be freely constructed with `OsRng`.
///
/// The implementation is provided by the [getrandom] crate. Refer to
/// [getrandom] documentation for details.
///
/// This struct is available as `rand_core::OsRng` and as `rand::rngs::OsRng`.
/// In both cases, this requires the crate feature `getrandom` or `std`
/// (enabled by default in `rand` but not in `rand_core`).
///
/// # Blocking and error handling
///
/// It is possible that when used during early boot the first call to `OsRng`
/// will block until the system's RNG is initialised. It is also possible
/// (though highly unlikely) for `OsRng` to fail on some platforms, most
/// likely due to system mis-configuration.
///
/// After the first successful call, it is highly unlikely that failures or
/// significant delays will occur (although performance should be expected to
/// be much slower than a user-space PRNG).
///
/// # Usage example
/// ```
/// use rand_core::{TryRngCore, OsRng};
///
/// let mut key = [0u8; 16];
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
        let mut buf = [0u8; 4];
        getrandom(&mut buf)?;
        Ok(u32::from_ne_bytes(buf))
    }

    #[inline]
    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        let mut buf = [0u8; 8];
        getrandom(&mut buf)?;
        Ok(u64::from_ne_bytes(buf))
    }

    #[inline]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Self::Error> {
        getrandom(dest)?;
        Ok(())
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
