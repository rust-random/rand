// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Entropy generator, or wrapper around external generators

use rand_core::{RngCore, CryptoRng, Error, impls};
use os::OsRng;
use jitter::JitterRng;

/// An interface returning random data from external source(s), provided
/// specifically for securely seeding algorithmic generators (PRNGs).
/// 
/// Where possible, `EntropyRng` retrieves random data from the operating
/// system's interface for random numbers ([`OsRng`]); if that fails it will
/// fall back to the [`JitterRng`] entropy collector. In the latter case it will
/// still try to use [`OsRng`] on the next usage.
/// 
/// If no secure source of entropy is available `EntropyRng` will panic on use;
/// i.e. it should never output predictable data.
/// 
/// This is either a little slow ([`OsRng`] requires a system call) or extremely
/// slow ([`JitterRng`] must use significant CPU time to generate sufficient
/// jitter); for better performance it is common to seed a local PRNG from
/// external entropy then primarily use the local PRNG ([`thread_rng`] is
/// provided as a convenient, local, automatically-seeded CSPRNG).
///
/// [`OsRng`]: os/struct.OsRng.html
/// [`JitterRng`]: jitter/struct.JitterRng.html
/// [`thread_rng`]: fn.thread_rng.html
#[derive(Debug)]
pub struct EntropyRng {
    rng: EntropySource,
}

#[derive(Debug)]
enum EntropySource {
    Os(OsRng),
    Jitter(JitterRng),
    None,
}

impl EntropyRng {
    /// Create a new `EntropyRng`.
    ///
    /// This method will do no system calls or other initialization routines,
    /// those are done on first use. This is done to make `new` infallible,
    /// and `try_fill_bytes` the only place to report errors.
    pub fn new() -> Self {
        EntropyRng { rng: EntropySource::None }
    }
}

impl Default for EntropyRng {
    fn default() -> Self {
        EntropyRng::new()
    }
}

impl RngCore for EntropyRng {
    fn next_u32(&mut self) -> u32 {
        impls::next_u32_via_fill(self)
    }

    fn next_u64(&mut self) -> u64 {
        impls::next_u64_via_fill(self)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.try_fill_bytes(dest).unwrap_or_else(|err|
                panic!("all entropy sources failed; first error: {}", err))
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        fn try_os_new(dest: &mut [u8]) -> Result<OsRng, Error>
        {
            let mut rng = OsRng::new()?;
            rng.try_fill_bytes(dest)?;
            Ok(rng)
        }

        fn try_jitter_new(dest: &mut [u8]) -> Result<JitterRng, Error>
        {
            let mut rng = JitterRng::new()?;
            rng.try_fill_bytes(dest)?;
            Ok(rng)
        }

        let mut switch_rng = None;
        match self.rng {
            EntropySource::None => {
                let os_rng_result = try_os_new(dest);
                match os_rng_result {
                    Ok(os_rng) => {
                        debug!("EntropyRng: using OsRng");
                        switch_rng = Some(EntropySource::Os(os_rng));
                    }
                    Err(os_rng_error) => {
                        warn!("EntropyRng: OsRng failed [falling back to JitterRng]: {}",
                              os_rng_error);
                        match try_jitter_new(dest) {
                            Ok(jitter_rng) => {
                                debug!("EntropyRng: using JitterRng");
                                switch_rng = Some(EntropySource::Jitter(jitter_rng));
                            }
                            Err(_jitter_error) => {
                                warn!("EntropyRng: JitterRng failed: {}",
                                      _jitter_error);
                                return Err(os_rng_error);
                            }
                        }
                    }
                }
            }
            EntropySource::Os(ref mut rng) => {
                let os_rng_result = rng.try_fill_bytes(dest);
                if let Err(os_rng_error) = os_rng_result {
                    warn!("EntropyRng: OsRng failed [falling back to JitterRng]: {}",
                          os_rng_error);
                    match try_jitter_new(dest) {
                        Ok(jitter_rng) => {
                            debug!("EntropyRng: using JitterRng");
                            switch_rng = Some(EntropySource::Jitter(jitter_rng));
                        }
                        Err(_jitter_error) => {
                            warn!("EntropyRng: JitterRng failed: {}",
                                  _jitter_error);
                            return Err(os_rng_error);
                        }
                    }
                }
            }
            EntropySource::Jitter(ref mut rng) => {
                if let Ok(os_rng) = try_os_new(dest) {
                    debug!("EntropyRng: using OsRng");
                    switch_rng = Some(EntropySource::Os(os_rng));
                } else {
                    return rng.try_fill_bytes(dest); // use JitterRng
                }
            }
        }
        if let Some(rng) = switch_rng {
            self.rng = rng;
        }
        Ok(())
    }
}

impl CryptoRng for EntropyRng {}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_entropy() {
        let mut rng = EntropyRng::new();
        let n = (rng.next_u32() ^ rng.next_u32()).count_ones();
        assert!(n >= 2);    // p(failure) approx 1e-7
    }
}
