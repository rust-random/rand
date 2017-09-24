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

use core::fmt::Debug;

use {Rng, SeedableRng, Result};
#[cfg(feature="std")]
use NewSeeded;

/// How many bytes of entropy the underling RNG is allowed to generate
/// before it is reseeded
const DEFAULT_GENERATION_THRESHOLD: u64 = 32 * 1024;

/// A wrapper around any RNG which reseeds the underlying RNG after it
/// has generated a certain number of random bytes.
#[derive(Debug)]
pub struct ReseedingRng<R, Rsdr: Debug> {
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
    pub fn reseed_if_necessary(&mut self) {
        if self.bytes_generated >= self.generation_threshold {
            self.reseeder.reseed(&mut self.rng);
            self.bytes_generated = 0;
        }
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

    fn try_fill(&mut self, dest: &mut [u8]) -> Result<()> {
        self.reseed_if_necessary();
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
pub trait Reseeder<R: ?Sized>: Debug {
    /// Reseed the given RNG.
    fn reseed(&mut self, rng: &mut R);
}

/// Reseed an RNG using `NewSeeded` to replace the current instance.
#[cfg(feature="std")]
#[derive(Clone, Copy, Debug)]
pub struct ReseedWithNew;

#[cfg(feature="std")]
impl<R: Rng + NewSeeded> Reseeder<R> for ReseedWithNew {
    fn reseed(&mut self, rng: &mut R) {
        match R::new() {
            Ok(result) => *rng = result,
            // TODO: should we ignore and continue without reseeding?
            Err(e) => panic!("Reseeding failed: {:?}", e),
        }
    }
}

#[cfg(test)]
mod test {
    use std::iter::repeat;
    use rand_core::mock::MockAddRng;
    use {SeedableRng, Rng, iter};
    use distributions::ascii_word_char;
    use super::{ReseedingRng, Reseeder};
    
    #[derive(Debug)]
    struct ReseedMock;
    impl Reseeder<MockAddRng<u32>> for ReseedMock {
        fn reseed(&mut self, rng: &mut MockAddRng<u32>) {
            *rng = MockAddRng::new(0, 1);
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
        let mut ra: MyRng = SeedableRng::from_seed((ReseedMock, 2));
        let mut rb: MyRng = SeedableRng::from_seed((ReseedMock, 2));
        assert!(::test::iter_eq(iter(&mut ra).map(|rng| ascii_word_char(rng)).take(100),
                                iter(&mut rb).map(|rng| ascii_word_char(rng)).take(100)));
    }

    const FILL_BYTES_V_LEN: usize = 13579;
    #[test]
    fn test_rng_try_fill() {
        let mut v = repeat(0u8).take(FILL_BYTES_V_LEN).collect::<Vec<_>>();
        ::test::rng().try_fill(&mut v).unwrap();

        // Sanity test: if we've gotten here, `try_fill` has not infinitely
        // recursed.
        assert_eq!(v.len(), FILL_BYTES_V_LEN);

        // To test that `try_fill` actually did something, check that the
        // average of `v` is not 0.
        let mut sum = 0.0;
        for &x in v.iter() {
            sum += x as f64;
        }
        assert!(sum / v.len() as f64 != 0.0);
    }
}
