// Copyright 2019 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Interface to the random number generator of the operating system.

use crate::{SeedableRng, TryCryptoRng, TryRngCore};

/// An interface over the operating-system's random data source
///
/// This is a zero-sized struct. It can be freely constructed with just `OsRng`.
///
/// The implementation is provided by the [getrandom] crate. Refer to
/// [getrandom] documentation for details.
///
/// This struct is available as `rand_core::OsRng` and as `rand::rngs::OsRng`.
/// In both cases, this requires the crate feature `os_rng` or `std`
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
/// be much slower than a user-space
/// [PRNG](https://rust-random.github.io/book/guide-gen.html#pseudo-random-number-generators)).
///
/// # Usage example
/// ```
/// use rand::{TryRngCore, rngs::OsRng};
///
/// let mut key = [0u8; 16];
/// OsRng.try_fill_bytes(&mut key).unwrap();
/// let random_u64 = OsRng.try_next_u64().unwrap();
/// ```
///
/// [getrandom]: https://crates.io/crates/getrandom
#[derive(Clone, Copy, Debug, Default)]
pub struct OsRng;

/// Error type of [`OsRng`]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OsError(getrandom::Error);

impl core::fmt::Display for OsError {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.0.fmt(f)
    }
}

// NOTE: this can use core::error::Error from rustc 1.81.0
#[cfg(feature = "std")]
impl std::error::Error for OsError {
    #[inline]
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        std::error::Error::source(&self.0)
    }
}

// If [`RawOsError`](https://doc.rust-lang.org/std/io/type.RawOsError.html) is stablized, we can use it.

#[cfg(not(target_os = "uefi"))]
type RawOsError = i32;

#[cfg(target_os = "uefi")]
type RawOsError = usize;

impl OsError {
    /// Extract the raw OS error code (if this error came from the OS)
    ///
    /// This method is identical to [`std::io::Error::raw_os_error()`][1], except
    /// that it works in `no_std` contexts. If this method returns `None`, the
    /// error value can still be formatted via the `Display` implementation.
    ///
    /// [1]: https://doc.rust-lang.org/std/io/struct.Error.html#method.raw_os_error
    #[inline]
    pub fn raw_os_error(self) -> Option<RawOsError> {
        self.0.raw_os_error()
    }
}

impl TryRngCore for OsRng {
    type Error = OsError;

    #[inline]
    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        getrandom::u32().map_err(OsError)
    }

    #[inline]
    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        getrandom::u64().map_err(OsError)
    }

    #[inline]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Self::Error> {
        getrandom::fill(dest).map_err(OsError)
    }
}

impl TryCryptoRng for OsRng {}

impl OsRng {
    /// Creates a new instance of the RNG `R` seeded via [`OsRng`].
    ///
    /// This method is the recommended way to construct non-deterministic PRNGs
    /// since it is convenient and secure.
    ///
    /// Note that this method may panic on (extremely unlikely) [`OsRng`] errors.
    /// If it's not desirable, use the [`OsRng::try_seed`] method instead.
    ///
    /// # Panics
    ///
    /// If [`OsRng`] is unable to provide secure entropy this method will panic.
    pub fn seed<R: SeedableRng>(&mut self) -> R {
        match self.try_seed::<R>() {
            Ok(res) => res,
            Err(err) => panic!("OsRng::try_seed failed: {}", err),
        }
    }

    /// Creates a new instance of the RNG `R` seeded via [`OsRng`], propagating any errors that may
    /// occur.
    pub fn try_seed<R: SeedableRng>(&mut self) -> Result<R, OsError> {
        let mut seed = R::Seed::default();
        self.try_fill_bytes(seed.as_mut())?;
        Ok(R::from_seed(seed))
    }
}

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
