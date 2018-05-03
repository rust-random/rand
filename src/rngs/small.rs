// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A small fast RNG

use {RngCore, SeedableRng, Error};
use prng::XorShiftRng;

/// An RNG recommended when small state, cheap initialization and good
/// performance are required. The PRNG algorithm in `SmallRng` is chosen to be
/// efficient on the current platform, **without consideration for cryptography
/// or security**. The size of its state is much smaller than for [`StdRng`].
///
/// Reproducibility of output from this generator is however not required, thus
/// future library versions may use a different internal generator with
/// different output. Further, this generator may not be portable and can
/// produce different output depending on the architecture. If you require
/// reproducible output, use a named RNG, for example [`XorShiftRng`].
///
/// The current algorithm used on all platforms is [Xorshift].
///
/// # Examples
///
/// Initializing `SmallRng` with a random seed can be done using [`FromEntropy`]:
///
/// ```
/// # use rand::Rng;
/// use rand::FromEntropy;
/// use rand::rngs::SmallRng;
///
/// // Create small, cheap to initialize and fast RNG with a random seed.
/// // The randomness is supplied by the operating system.
/// let mut small_rng = SmallRng::from_entropy();
/// # let v: u32 = small_rng.gen();
/// ```
///
/// When initializing a lot of `SmallRng`'s, using [`thread_rng`] can be more
/// efficient:
///
/// ```
/// use std::iter;
/// use rand::{SeedableRng, thread_rng};
/// use rand::rngs::SmallRng;
///
/// // Create a big, expensive to initialize and slower, but unpredictable RNG.
/// // This is cached and done only once per thread.
/// let mut thread_rng = thread_rng();
/// // Create small, cheap to initialize and fast RNGs with random seeds.
/// // One can generally assume this won't fail.
/// let rngs: Vec<SmallRng> = iter::repeat(())
///     .map(|()| SmallRng::from_rng(&mut thread_rng).unwrap())
///     .take(10)
///     .collect();
/// ```
///
/// [`FromEntropy`]: ../trait.FromEntropy.html
/// [`StdRng`]: struct.StdRng.html
/// [`thread_rng`]: ../fn.thread_rng.html
/// [Xorshift]: ../prng/struct.XorShiftRng.html
/// [`XorShiftRng`]: ../prng/struct.XorShiftRng.html
#[derive(Clone, Debug)]
pub struct SmallRng(XorShiftRng);

impl RngCore for SmallRng {
    #[inline(always)]
    fn next_u32(&mut self) -> u32 {
        self.0.next_u32()
    }

    #[inline(always)]
    fn next_u64(&mut self) -> u64 {
        self.0.next_u64()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.0.fill_bytes(dest);
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        self.0.try_fill_bytes(dest)
    }
}

impl SeedableRng for SmallRng {
    type Seed = <XorShiftRng as SeedableRng>::Seed;

    fn from_seed(seed: Self::Seed) -> Self {
        SmallRng(XorShiftRng::from_seed(seed))
    }

    fn from_rng<R: RngCore>(rng: R) -> Result<Self, Error> {
        XorShiftRng::from_rng(rng).map(SmallRng)
    }
}
