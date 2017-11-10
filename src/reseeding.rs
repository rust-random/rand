// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A wrapper around another RNG that reseeds it after it
//! generates a certain number of random bytes.

use core::cmp::max;
use {Rng, SeedableRng, Error, ErrorKind};
#[cfg(feature="std")]
use NewSeeded;

/// How many bytes of entropy the underling RNG is allowed to generate
/// before it is reseeded
const DEFAULT_GENERATION_THRESHOLD: u64 = 32 * 1024;

/// A wrapper around any RNG which reseeds the underlying RNG after it
/// has generated a certain number of random bytes.
/// 
/// Note that reseeding is considered advisory only. If reseeding fails, the
/// generator may delay reseeding or not reseed at all.
/// 
/// This derives `Clone` if both the inner RNG `R` and the reseeder `Rsdr` do.
/// Note that reseeders using external entropy should deliberately not
/// implement `Clone`.
#[derive(Debug, Clone)]
pub struct ReseedingRng<R, Rsdr: Reseeder<R>> {
    rng: R,
    generation_threshold: u64,
    bytes_generated: u64,
    /// Controls the behaviour when reseeding the RNG.
    pub reseeder: Rsdr,
}

impl<R: Rng, Rsdr: Reseeder<R>> ReseedingRng<R, Rsdr> {
    /// Create a new `ReseedingRng` with the given parameters.
    ///
    /// # Arguments
    ///
    /// * `rng`: the random number generator to use.
    /// * `generation_threshold`: the number of bytes of entropy at which to reseed the RNG.
    /// * `reseeder`: the reseeding object to use.
    pub fn new(rng: R, generation_threshold: u64, reseeder: Rsdr) -> ReseedingRng<R,Rsdr> {
        ReseedingRng {
            rng: rng,
            generation_threshold: generation_threshold,
            bytes_generated: 0,
            reseeder: reseeder
        }
    }

    /// Reseed the internal RNG if the number of bytes that have been
    /// generated exceed the threshold.
    /// 
    /// On error, this may delay reseeding or not reseed at all.
    pub fn reseed_if_necessary(&mut self) {
        if self.bytes_generated >= self.generation_threshold {
            let mut err_count = 0;
            loop {
                if let Err(e) = self.reseeder.reseed(&mut self.rng) {
                    // TODO: log?
                    if e.kind.should_wait() {
                        // Delay reseeding
                        let delay = max(self.generation_threshold >> 8, self.bytes_generated);
                        self.bytes_generated -= delay;
                        break;
                    } else if e.kind.should_retry() {
                        if err_count > 4 {  // arbitrary limit
                            // TODO: log details & cause?
                            break;  // give up trying to reseed
                        }
                        err_count += 1;
                        continue;   // immediate retry
                    } else {
                        break;  // give up trying to reseed
                    }
                } else {
                    break;  // no reseeding
                }
            }
            self.bytes_generated = 0;
        }
    }
    /// Reseed the internal RNG if the number of bytes that have been
    /// generated exceed the threshold.
    /// 
    /// If reseeding fails, return an error with the original cause. Note that
    /// if the cause has a permanent failure, we report a transient error and
    /// skip reseeding.
    pub fn try_reseed_if_necessary(&mut self) -> Result<(), Error> {
        if self.bytes_generated >= self.generation_threshold {
            if let Err(err) = self.reseeder.reseed(&mut self.rng) {
                let newkind = match err.kind {
                    a @ ErrorKind::NotReady => a,
                    b @ ErrorKind::Transient => b,
                    _ => {
                        self.bytes_generated = 0;   // skip reseeding
                        ErrorKind::Transient
                    }
                };
                return Err(Error::new_with_cause(newkind, "reseeding failed", err));
            }
            self.bytes_generated = 0;
        }
        Ok(())
    }
}


impl<R: Rng, Rsdr: Reseeder<R>> Rng for ReseedingRng<R, Rsdr> {
    fn next_u32(&mut self) -> u32 {
        self.reseed_if_necessary();
        self.bytes_generated += 4;
        self.rng.next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        self.reseed_if_necessary();
        self.bytes_generated += 8;
        self.rng.next_u64()
    }

    #[cfg(feature = "i128_support")]
    fn next_u128(&mut self) -> u128 {
        self.reseed_if_necessary();
        self.bytes_generated += 16;
        self.rng.next_u128()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.reseed_if_necessary();
        self.bytes_generated += dest.len() as u64;
        self.rng.fill_bytes(dest);
    }

    fn try_fill(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        self.try_reseed_if_necessary()?;
        self.bytes_generated += dest.len() as u64;
        self.rng.try_fill(dest)
    }
}

impl<S, R: SeedableRng<S>, Rsdr: Reseeder<R>> SeedableRng<(Rsdr, S)> for
        ReseedingRng<R, Rsdr>
{
    /// Create a new `ReseedingRng` from the given reseeder and
    /// seed. This uses a default value for `generation_threshold`.
    fn from_seed((rsdr, seed): (Rsdr, S)) -> ReseedingRng<R, Rsdr> {
        ReseedingRng {
            rng: SeedableRng::from_seed(seed),
            generation_threshold: DEFAULT_GENERATION_THRESHOLD,
            bytes_generated: 0,
            reseeder: rsdr
        }
    }
}

/// Something that can be used to reseed an RNG via `ReseedingRng`.
/// 
/// Note that implementations should support `Clone` only if reseeding is
/// deterministic (no external entropy source). This is so that a `ReseedingRng`
/// only supports `Clone` if fully deterministic.
pub trait Reseeder<R: ?Sized> {
    /// Reseed the given RNG.
    /// 
    /// On error, this should just forward the source error; errors are handled
    /// by the caller.
    fn reseed(&mut self, rng: &mut R) -> Result<(), Error>;
}

/// Reseed an RNG using `NewSeeded` to replace the current instance.
#[cfg(feature="std")]
#[derive(Debug)]
pub struct ReseedWithNew;

#[cfg(feature="std")]
impl<R: Rng + NewSeeded> Reseeder<R> for ReseedWithNew {
    fn reseed(&mut self, rng: &mut R) -> Result<(), Error> {
        R::new().map(|result| *rng = result)
    }
}

#[cfg(test)]
mod test {
    use std::iter::repeat;
    use mock::MockAddRng;
    use {SeedableRng, Rng, iter, Error};
    use super::{ReseedingRng, Reseeder};
    
    #[derive(Debug, Clone)]
    struct ReseedMock;
    impl Reseeder<MockAddRng<u32>> for ReseedMock {
        fn reseed(&mut self, rng: &mut MockAddRng<u32>) -> Result<(), Error> {
            *rng = MockAddRng::new(0, 1);
            Ok(())
        }
    }

    type MyRng = ReseedingRng<MockAddRng<u32>, ReseedMock>;

    #[test]
    fn test_reseeding() {
        let mut rs = ReseedingRng::new(MockAddRng::new(0, 1), 400, ReseedMock);

        let mut i = 0;
        for _ in 0..1000 {
            assert_eq!(rs.next_u32(), i % 100);
            i += 1;
        }
    }

    #[test]
    fn test_rng_seeded() {
        // Default seed threshold is way beyond what we use here
        let mut ra: MyRng = SeedableRng::from_seed((ReseedMock, 2));
        let mut rb: MockAddRng<u32> = SeedableRng::from_seed(2);
        assert!(::test::iter_eq(iter(&mut ra).map(|rng| rng.next_u32()).take(100),
                                iter(&mut rb).map(|rng| rng.next_u32()).take(100)));
    }

    const FILL_BYTES_V_LEN: usize = 13579;
    #[test]
    fn test_rng_fill_bytes() {
        let mut v = repeat(0u8).take(FILL_BYTES_V_LEN).collect::<Vec<_>>();
        ::test::rng().fill_bytes(&mut v);

        // Sanity test: if we've gotten here, `fill_bytes` has not infinitely
        // recursed.
        assert_eq!(v.len(), FILL_BYTES_V_LEN);

        // To test that `fill_bytes` actually did something, check that the
        // average of `v` is not 0.
        let mut sum = 0.0;
        for &x in v.iter() {
            sum += x as f64;
        }
        assert!(sum / v.len() as f64 != 0.0);
    }
}
