// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A small fast RNG

use rand_core::{RngCore, SeedableRng};

#[cfg(target_pointer_width = "64")]
type Rng = super::xoshiro256plusplus::Xoshiro256PlusPlus;
#[cfg(not(target_pointer_width = "64"))]
type Rng = super::xoshiro128plusplus::Xoshiro128PlusPlus;

/// A small-state, fast, non-crypto, non-portable PRNG
///
/// This is the "standard small" RNG, a generator with the following properties:
///
/// - Non-[portable]: any future library version may replace the algorithm
///   and results may be platform-dependent.
///   (For a small portable generator, use the [rand_pcg] or [rand_xoshiro] crate.)
/// - Non-cryptographic: output is easy to predict (insecure)
/// - [Quality]: statistically good quality
/// - Fast: the RNG is fast for both bulk generation and single values, with
///   consistent cost of method calls
/// - Fast initialization
/// - Small state: little memory usage (current state size is 16-32 bytes
///   depending on platform)
///
/// The current algorithm is
/// `Xoshiro256PlusPlus` on 64-bit platforms and `Xoshiro128PlusPlus` on 32-bit
/// platforms. Both are also implemented by the [rand_xoshiro] crate.
///
/// ## Seeding (construction)
///
/// This generator implements the [`SeedableRng`] trait. All methods are
/// suitable for seeding, but note that, even with a fixed seed, output is not
/// [portable]. Some suggestions:
///
/// 1.  Seed **from an integer** via `seed_from_u64`. This uses a hash function
///     internally to yield a (typically) good seed from any input.
///     ```
///     # use rand::{SeedableRng, rngs::SmallRng};
///     let rng = SmallRng::seed_from_u64(1);
///     # let _: SmallRng = rng;
///     ```
/// 2.  With a fresh seed, **direct from the OS** (implies a syscall):
///     ```
///     # use rand::{SeedableRng, rngs::SmallRng};
///     let rng = SmallRng::from_os_rng();
///     # let _: SmallRng = rng;
///     ```
/// 3.  **From a master generator.** This could be [`thread_rng`][crate::thread_rng]
///     (effectively a fresh seed without the need for a syscall on each usage)
///     or a deterministic generator such as [`rand_chacha::ChaCha8Rng`].
///     Beware that should a weak master generator be used, correlations may be
///     detectable between the outputs of its child generators.
///
/// See also [Seeding RNGs] in the book.
///
/// ## Generation
///
/// The generators implements [`RngCore`] and thus also [`Rng`][crate::Rng].
/// See also the [Random Values] chapter in the book.
///
/// [portable]: https://rust-random.github.io/book/crate-reprod.html
/// [Seeding RNGs]: https://rust-random.github.io/book/guide-seeding.html
/// [Random Values]: https://rust-random.github.io/book/guide-values.html
/// [Quality]: https://rust-random.github.io/book/guide-rngs.html#quality
/// [`StdRng`]: crate::rngs::StdRng
/// [rand_pcg]: https://crates.io/crates/rand_pcg
/// [rand_xoshiro]: https://crates.io/crates/rand_xoshiro
/// [`rand_chacha::ChaCha8Rng`]: https://docs.rs/rand_chacha/latest/rand_chacha/struct.ChaCha8Rng.html
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
        self.0.fill_bytes(dest)
    }
}

rand_core::impl_try_rng_from_rng_core!(SmallRng);

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
    pub fn from_rng<R: RngCore>(rng: R) -> Self {
        Self(Rng::from_rng(rng))
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
