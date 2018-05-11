// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Pseudo random number generators are algorithms to produce *apparently
//! random* numbers deterministically, and usually fairly quickly.
//!
//! So long as the algorithm is computationally secure, is initialised with
//! sufficient entropy (i.e. unknown by an attacker), and its internal state is
//! also protected (unknown to an attacker), the output will also be
//! *computationally secure*. Computationally Secure Pseudo Random Number
//! Generators (CSPRNGs) are thus suitable sources of random numbers for
//! cryptography. There are a couple of gotchas here, however. First, the seed
//! used for initialisation must be unknown. Usually this should be provided by
//! the operating system and should usually be secure, however this may not
//! always be the case (especially soon after startup). Second, user-space
//! memory may be vulnerable, for example when written to swap space, and after
//! forking a child process should reinitialise any user-space PRNGs. For this
//! reason it may be preferable to source random numbers directly from the OS
//! for cryptographic applications.
//!
//! PRNGs are also widely used for non-cryptographic uses: randomised
//! algorithms, simulations, games. In these applications it is usually not
//! important for numbers to be cryptographically *unguessable*, but even
//! distribution and independence from other samples (from the point of view
//! of someone unaware of the algorithm used, at least) may still be important.
//! Good PRNGs should satisfy these properties, but do not take them for
//! granted; Wikipedia's article on
//! [Pseudorandom number generators](https://en.wikipedia.org/wiki/Pseudorandom_number_generator)
//! provides some background on this topic.
//!
//! Care should be taken when seeding (initialising) PRNGs. Some PRNGs have
//! short periods for some seeds. If one PRNG is seeded from another using the
//! same algorithm, it is possible that both will yield the same sequence of
//! values (with some lag).
//!
//! ## Cryptographic security
//!
//! First, lets recap some terminology:
//!
//! - **PRNG:** *Pseudo-Random-Number-Generator* is another name for an
//!   *algorithmic generator*
//! - **CSPRNG:** a *Cryptographically Secure* PRNG
//!
//! Security analysis requires a threat model and expert review; we can provide
//! neither, but we can provide a few hints. We assume that the goal is to
//! produce secret apparently-random data. Therefore, we need:
//!
//! - A good source of entropy. A known algorithm given known input data is
//!   trivial to predict, and likewise if there's a non-negligable chance that
//!   the input to a PRNG is guessable then there's a chance its output is too.
//!   We recommend seeding CSPRNGs with [`EntropyRng`] or [`OsRng`] which
//!   provide fresh "random" values from an external source.
//!   One can also seed from another CSPRNG, e.g. [`thread_rng`], which is faster,
//!   but adds another component which must be trusted.
//! - A strong algorithmic generator. It is possible to use a good entropy
//!   source like [`OsRng`] directly, and in some cases this is the best option,
//!   but for better performance (or if requiring reproducible values generated
//!   from a fixed seed) it is common to use a local CSPRNG. The basic security
//!   that CSPRNGs must provide is making it infeasible to predict future output
//!   given a sample of past output. A further security that *some* CSPRNGs
//!   provide is *forward secrecy*; this ensures that in the event that the
//!   algorithm's state is revealed, it is infeasible to reconstruct past
//!   output. See the [`CryptoRng`] trait and notes on individual algorithms.
//! - To be careful not to leak secrets like keys and CSPRNG's internal state
//!   and robust against "side channel attacks". This goes well beyond the scope
//!   of random number generation, but this crate takes some precautions:
//!   - to avoid printing CSPRNG state in log files, implementations have a
//!     custom `Debug` implementation which omits all internal state
//!   - [`thread_rng`] uses [`ReseedingRng`] to periodically refresh its state
//!   - in the future we plan to add some protection against fork attacks
//!     (where the process is forked and each clone generates the same "random"
//!     numbers); this is not yet implemented (see issues #314, #370)
//!
//! [`CryptoRng`]: ../trait.CryptoRng.html
//! [`EntropyRng`]: ../rngs/struct.EntropyRng.html
//! [`OsRng`]: ../rngs/struct.OsRng.html
//! [`ReseedingRng`]: ../rngs/adaptor/struct.ReseedingRng.html
//! [`thread_rng`]: ../fn.thread_rng.html

pub mod chacha;
pub mod hc128;
pub mod isaac;
pub mod isaac64;
mod xorshift;

mod isaac_array;

pub use self::chacha::ChaChaRng;
pub use self::hc128::Hc128Rng;
pub use self::isaac::IsaacRng;
pub use self::isaac64::Isaac64Rng;
pub use self::xorshift::XorShiftRng;
