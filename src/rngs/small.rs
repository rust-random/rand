// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A small fast RNG

use rand_core::{Error, RngCore, SeedableRng};

#[cfg(target_pointer_width = "64")]
type Rng = super::xoshiro256plusplus::Xoshiro256PlusPlus;
#[cfg(not(target_pointer_width = "64"))]
type Rng = super::xoshiro128plusplus::Xoshiro128PlusPlus;

/// A small-state, fast non-crypto PRNG
///
/// `SmallRng` may be a good choice when a PRNG with small state, cheap
/// initialization, good statistical quality and good performance are required.
/// Note that depending on the application, [`StdRng`] may be faster on many
/// modern platforms while providing higher-quality randomness. Furthermore,
/// `SmallRng` is **not** a good choice when:
///
/// - Portability is required. Its implementation is not fixed. Use a named
///   generator from an external crate instead, for example [rand_xoshiro] or
///   [rand_chacha]. Refer also to
///   [The Book](https://rust-random.github.io/book/guide-rngs.html).
/// - Security against prediction is important. Use [`StdRng`] instead.
///
/// The PRNG algorithm in `SmallRng` is chosen to be efficient on the current
/// platform, without consideration for cryptography or security. The size of
/// its state is much smaller than [`StdRng`]. The current algorithm is
/// `Xoshiro256PlusPlus` on 64-bit platforms and `Xoshiro128PlusPlus` on 32-bit
/// platforms. Both are also implemented by the [rand_xoshiro] crate.
///
/// [`StdRng`]: crate::rngs::StdRng
/// [rand_chacha]: https://crates.io/crates/rand_chacha
/// [rand_xoshiro]: https://crates.io/crates/rand_xoshiro
#[cfg_attr(doc_cfg, doc(cfg(feature = "small_rng")))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SmallRng(Rng);

impl RngCore for SmallRng {
    #[inline(always)]
    fn next_u32(&mut self) -> u32 {
        self.0.next_u32()
    }

    #[inline(always)]
    fn next_u64(&mut self) -> u64 {
        self.0.next_u64()
    }

    #[inline(always)]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.0.fill_bytes(dest);
    }

    #[inline(always)]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        self.0.try_fill_bytes(dest)
    }
}

impl SmallRng {
    /// Construct an instance seeded from another `Rng`
    ///
    /// We recommend that the source (master) RNG uses a different algorithm
    /// (i.e. is not `SmallRng`) to avoid correlations between the child PRNGs.
    ///
    /// # Example
    /// ```
    /// # use rand::rngs::SmallRng;
    /// let rng = SmallRng::from_rng(rand::thread_rng());
    /// ```
    #[inline(always)]
    pub fn from_rng<R: RngCore>(rng: R) -> Result<Self, Error> {
        Rng::from_rng(rng).map(SmallRng)
    }

    /// Construct an instance seeded from the thread-local RNG
    ///
    /// # Panics
    ///
    /// This method panics only if [`thread_rng`](crate::thread_rng) fails to
    /// initialize.
    #[cfg(all(feature = "std", feature = "std_rng", feature = "getrandom"))]
    #[inline(always)]
    pub fn from_thread_rng() -> Self {
        let mut seed = <Rng as SeedableRng>::Seed::default();
        crate::thread_rng().fill_bytes(seed.as_mut());
        SmallRng(Rng::from_seed(seed))
    }

    /// Construct an instance from a `u64` seed
    ///
    /// This provides a convenient method of seeding a `SmallRng` from a simple
    /// number by use of another algorithm to mutate and expand the input.
    /// This is suitable for use with low Hamming Weight numbers like 0 and 1.
    ///
    /// **Warning:** the implementation is deterministic but not portable:
    /// output values may differ according to platform and may be changed by a
    /// future version of the library.
    ///
    /// # Example
    /// ```
    /// # use rand::rngs::SmallRng;
    /// let rng = SmallRng::seed_from_u64(1);
    /// ```
    #[inline(always)]
    pub fn seed_from_u64(state: u64) -> Self {
        SmallRng(Rng::seed_from_u64(state))
    }
}
