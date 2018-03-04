// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A wrapper around another PRNG that reseeds it after it
//! generates a certain number of random bytes.

use rand_core::{RngCore, BlockRngCore, SeedableRng, Error, ErrorKind};
use rand_core::impls::BlockRng;

/// A wrapper around any PRNG which reseeds the underlying PRNG after it has
/// generated a certain number of random bytes.
///
/// Reseeding is never strictly *necessary*. Cryptographic PRNGs don't have a
/// limited number of bytes they can output, or at least not a limit reachable
/// in any practical way. There is no such thing as 'running out of entropy'.
///
/// Some small non-cryptographic PRNGs can have very small periods, for
/// example less than 2<sup>64</sup>. Would reseeding help to ensure that you do
/// not wrap around at the end of the period? A period of 2<sup>64</sup> still
/// takes several centuries of CPU-years on current hardware. Reseeding will
/// actually make things worse, because the reseeded PRNG will just continue
/// somewhere else *in the same period*, with a high chance of overlapping with
/// previously used parts of it.
///
/// # When should you use `ReseedingRng`?
///
/// - Reseeding can be seen as some form of 'security in depth'. Even if in the
///   future a cryptographic weakness is found in the CSPRNG being used,
///   occasionally reseeding should make exploiting it much more difficult or
///   even impossible.
/// - It can be used as a poor man's cryptography (not recommended, just use a
///   good CSPRNG). Previous implementations of `thread_rng` for example used
///   `ReseedingRng` with the ISAAC RNG. That algorithm, although apparently
///   strong and with no known attack, does not come with any proof of security
///   and does not meet the current standards for a cryptographically secure
///   PRNG. By reseeding it frequently (every 32 kiB) it seems safe to assume
///   there is no attack that can operate on the tiny window between reseeds.
///
/// # Error handling
///
/// If reseeding fails, `try_fill_bytes` is the only `Rng` method to report it.
/// For all other `Rng` methods, `ReseedingRng` will not panic but try to
/// handle the error intelligently through some combination of retrying and
/// delaying reseeding until later. If handling the source error fails these
/// methods will continue generating data from the wrapped PRNG without
/// reseeding.
#[derive(Debug)]
pub struct ReseedingRng<R, Rsdr>(BlockRng<Reseeder<R, Rsdr>>)
where R: BlockRngCore<u32> + SeedableRng,
      Rsdr: RngCore;

impl<R, Rsdr> ReseedingRng<R, Rsdr>
where R: BlockRngCore<u32> + SeedableRng,
      Rsdr: RngCore
{
    /// Create a new `ReseedingRng` with the given parameters.
    ///
    /// # Arguments
    ///
    /// * `rng`: the random number generator to use.
    /// * `threshold`: the number of generated bytes after which to reseed the RNG.
    /// * `reseeder`: the RNG to use for reseeding.
    pub fn new(rng: R, threshold: u64, reseeder: Rsdr)
        -> ReseedingRng<R, Rsdr>
    {
        assert!(threshold <= ::core::i64::MAX as u64);
        let results_empty = R::Results::default();
        ReseedingRng(
            BlockRng {
                core: Reseeder {
                    core: rng,
                    reseeder: reseeder,
                    threshold: threshold as i64,
                    bytes_until_reseed: threshold as i64,
                },
                index: results_empty.as_ref().len(), // generate on first use
                results: results_empty,
            }
        )
    }

    /// Reseed the internal PRNG.
    pub fn reseed(&mut self) -> Result<(), Error> {
        self.0.core.reseed()
    }
}

impl<R: BlockRngCore<u32> + SeedableRng, Rsdr: RngCore> RngCore for ReseedingRng<R, Rsdr> {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        self.0.next_u32()
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        self.0.next_u64()
    }

    #[inline]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.0.fill_bytes(dest)
    }

    #[inline]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        self.0.try_fill_bytes(dest)
    }
}

#[derive(Debug)]
struct Reseeder<R, Rsdr> {
    core: R,
    reseeder: Rsdr,
    threshold: i64,
    bytes_until_reseed: i64,
}

impl<R, Rsdr> BlockRngCore<u32> for Reseeder<R, Rsdr>
where R: BlockRngCore<u32> + SeedableRng,
      Rsdr: RngCore
{
    type Results = <R as BlockRngCore<u32>>::Results;

    fn generate(&mut self, results: &mut Self::Results) -> Result<(), Error> {
        if self.bytes_until_reseed <= 0 {
            // We want to reseed here, and generate results later in the
            // function. If generating results fail, we should return the error
            // from that. If generating results succeeded, but reseeding failed,
            // we should return the error from reseeding.
            // The only way to get this behaviour without destroying performance
            // was to split part of the function out into a
            // `reseed_and_generate` method.
            return self.reseed_and_generate(results);
        }
        self.bytes_until_reseed -= results.as_ref().len() as i64 * 4;
        self.core.generate(results)
    }
}

impl<R, Rsdr> Reseeder<R, Rsdr>
where R: BlockRngCore<u32> + SeedableRng,
      Rsdr: RngCore
{
    /// Reseed the internal PRNG.
    fn reseed(&mut self) -> Result<(), Error> {
        R::from_rng(&mut self.reseeder).map(|result| self.core = result)
    }

    /// Reseed the internal PRNG.
    ///
    /// If reseeding fails, this will try to work around errors intelligently
    /// through some combination of retrying and delaying reseeding until later.
    /// It will also report the error with `ErrorKind::Transient` with the
    /// original error as cause.
    fn auto_reseed(&mut self) -> Result<(), Error> {
        trace!("Reseeding RNG after {} generated bytes",
               self.threshold - self.bytes_until_reseed);
        if let Err(mut e) = self.reseed()  {
            let delay = match e.kind {
                ErrorKind::Transient => 0,
                kind @ _ if kind.should_retry() => self.threshold >> 8,
                _ => self.threshold,
            };
            warn!("Reseeding RNG delayed reseeding by {} bytes due to \
                    error from source: {}", delay, e);
            self.bytes_until_reseed = delay;
            e.kind = ErrorKind::Transient;
            Err(e)
        } else {
            self.bytes_until_reseed = self.threshold;
            Ok(())
        }
    }

    #[inline(never)]
    fn reseed_and_generate(&mut self,
                           results: &mut <Self as BlockRngCore<u32>>::Results)
        -> Result<(), Error>
    {
        let res1 = self.auto_reseed();
        self.bytes_until_reseed -= results.as_ref().len() as i64 * 4;
        let res2 = self.core.generate(results);
        if res2.is_err() { res2 } else { res1 }
    }
}

#[cfg(test)]
mod test {
    use {Rng, SeedableRng};
    use prng::chacha::ChaChaCore;
    use mock::StepRng;
    use super::ReseedingRng;

    #[test]
    fn test_reseeding() {
        let mut zero = StepRng::new(0, 0);
        let rng = ChaChaCore::from_rng(&mut zero).unwrap();
        let mut reseeding = ReseedingRng::new(rng, 32*4, zero);

        // Currently we only support for arrays up to length 32.
        // TODO: cannot generate seq via Rng::gen because it uses different alg
        let mut buf = [0u32; 32]; // Needs to be a multiple of the RNGs result
                                  // size to test exactly.
        reseeding.fill(&mut buf);
        let seq = buf;
        for _ in 0..10 {
            reseeding.fill(&mut buf);
            assert_eq!(buf, seq);
        }
    }
}
