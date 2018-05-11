// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Pseudo-random number generators.
//!
//! Pseudo-random number generators are algorithms to produce apparently random
//! numbers deterministically, and usually fairly quickly. See the documentation
//! of the [`rngs` module] for some introduction to PRNGs.
//!
//! As mentioned there, PRNGs fall in two broad categories:
//!
//! - [normal PRNGs], primarily designed for simulations.
//! - [CSPRNGs], primarily designed for cryptography.
//!
//! This module provides a few different PRNG implementations, and the
//! documentation aims to provide enough background to make a reasonably
//! informed choice.
//!
//!
//! # Normal pseudo-random number generators (PRNGs)
//!
//! The goal of normal PRNGs is usually to find a good balance between
//! simplicity, quality and performance. They are generally developed for doing
//! simulations, but the good performance and simplicity make them suitable for
//! many common programming problems.
//!
//! Mathematical theory is involved to ensure certain properties of the PRNG,
//! most notably to prove that it doesn't cycle before generating all values in
//! its period once.
//!
//! Usually there are three properties of a PRNG to consider:
//!
//! - performance
//! - quality
//! - extra features
//!
//! Currently Rand provides only one PRNG, and not a very good one at that:
//! [`XorShiftRng`].
//!
//!
//! ## Performance
//!
//! First it has to be said most PRNGs are really incredibly fast, and will
//! rarely be a performance bottleneck. Performance of PRNGs is however a bit of
//! a subtle thing. It depends much on the CPU architecture (32 vs. 64 bits),
//! inlining, but also on the number available of registers, which makes
//! performance dependent on the surrounding code.
//!
//! Some PRNGs are plain and simple faster than others, thanks to using cheaper
//! instructions, shuffling around less state etc. But when absolute performance
//! is a goal, benchmarking a few different PRNGs with your specific use case is
//! always recommended.
//!
//!
//! ## Quality
//!
//! Many PRNGs are not much more than a couple of bitwise and arithmetic
//! operations. Their simplicity gives good performance, but also means there
//! are small regularities hidden in the generated random number stream.
//!
//! How much do those hidden regularities matter? That is hard to say, and
//! depends on how the RNG gets used. If there happen to be correlations between
//! the random numbers and the algorithm they are used in, the results can be
//! wrong or misleading.
//!
//! A random number generator can be considered good if it gives the correct
//! results in as many applications as possible. There are test suites designed
//! to test how well a PRNG performs on a wide range of possible uses, the
//! latest and most complete of which are [TestU01] and [PractRand].
//!
//! It is easy to measure whether the PRNG is an actual performance bottleneck,
//! but hard to measure that generated values are as random as you expect them
//! to be. Then the safe choice is to use an RNG that performs well on the
//! empirical RNG tests.
//!
//! In other situations is is clear that some small hidden regularities are of
//! no concern. In that case, just choose a fast PRNG.
//!
//!
//! ## Extra features
//!
//! Some PRNGs may provide extra features, which can be a reason to prefer that
//! algorithm over others. Examples include:
//!
//! - Support for multiple streams, which helps with parallel tasks;
//! - The ability to jump or seek around in the random number stream.
//! - The algorithm uses some chaotic process, which will usually produce much
//!   more random-looking numbers, at the cost of loosing the ability to reason
//!   about things like it's period.
//! - Given previous values, the next value may be predictable, but not
//!   trivially.
//! - Having a huge period.
//!
//! ## Period
//!
//! The period of a PRNG is the number of values after which it starts repeating
//! the same random number stream. While an important property, it will usually
//! be of little concern as modern PRNGs just satisfy it.
//!
//! On today's hardware, even a fast RNG  with a period of only 2<sup>64</sup>
//! can be used for centuries before wrapping around. Yet we recommend a period
//! of 2<sup>128</sup> or more, which most modern PRNGs satisfy. Or a shorter
//! period, but support for multiple streams. Two reasons:
//!
//! If we see the entire period of an RNG as one long random number stream,
//! every independently seeded RNG returns a slice of that stream. When multiple
//! RNG are seeded randomly, there is an increasingly large chance to end up
//! with a partially overlapping slice of the stream.
//!
//! If the period of the RNG is 2<sup>128</sup>, and we take 2<sup>48</sup> as
//! the number of values usually consumed, it then takes about 2<sup>32</sup>
//! random initializations to have a chance of 1 in a million to repeat part of
//! an already used stream. Something that seems good enough for common use. As
//! an estimation, `chance ~= 1-e^((-initializations^2)/(2*period/used))`.
//!
//! Also not the entire period of an RNG should be used. The RNG produces every
//! possible value exactly the same number of times. This is not a property of
//! true randomness, it is natural to expect some variation in how often values
//! appear. This is known as the generalized birthday problem, see the
//! [PCG paper] for a good explanation. It becomes noticable after generating
//! more values than the root of the period (after 2<sup>64</sup> values for a
//! period of 2<sup>128</sup>).
//!
//!
//! # Cryptographically secure pseudo-random number generators (CSPRNGs)
//!
//! CSPRNGs have much higher requirements than normal PRNGs. The primary
//! consideration is security. Performance and simplicity are also important,
//! but in general CSPRNGs are more complex and slower than normal PRNGs.
//! Quality is no longer a concern, as it is a requirement for a
//! CSPRNG that the output is basically indistinguishable from true randomness,
//! otherwise information could be leaked.
//!
//! There is a relation between CSPRNGs and cryptographic ciphers.
//! One way to create a CSPRNG is to take a block cipher and to run in it
//! counter mode, i.e. to encrypt a simple counter. Another option is to take a
//! stream cipher, but to just leave out the part where it is combined (usually
//! XOR-ed) with the plaintext.
//!
//! Rand currently provides two CSPRNGs:
//!
//! - [`ChaChaRng`]. A reasonable fast RNG using little memory, which works
//!   by encrypting a counter. Based on the ChaCha20 stream cipher.
//! - [`Hc128Rng`]. A very fast array-based RNG that requires a lot of memory,
//!   4 KiB. Based on the HC-128 stream cipher.
//!
//! Since the beginning of randomness support in Rust an RNG based on the ISAAC
//! algorithm ([`IsaacRng`]) has been available. This an example of an algorithm
//! advertised as secure (which it very well may be), but which since its design
//! in 1996 never really attracted the attention of cryptography experts.
//!
//!
//! ## Security
//!
//! The basic security that CSPRNGs must provide is making it infeasible to
//! predict future output given a sample of past output. A further security that
//! some CSPRNGs provide is *forward secrecy*; this ensures that in the event
//! that the algorithm's state is revealed, it is infeasible to reconstruct past
//! output.
//!
//! As an outsider it is hard to get a good idea about the security of an
//! algorithm. People in the field of cryptography spend a lot of effort
//! analyzing existing designs, and what was once considered good may now turn
//! out to be weaker. Generally it is best to use algorithms well-analyzed by
//! experts. Not the very latest design, and also not older algorithms that
//! gained little attention. In practice it is best to just use algorithms
//! recommended by reputable organizations, such as the ciphers selected by the
//! eSTREAM contest, or some of those recommended by NIST.
//!
//! It is important to use a good source of entropy to get the seed for a
//! CSPRNG. When a known algorithm is given known input data, it is trivial to
//! predict. Likewise if there's a non-negligible chance that the input to a
//! PRNG is guessable, then there's a chance its output is too. We recommend
//! seeding CSPRNGs using the [`FromEntropy`] trait, which uses fresh random
//! values from an external source, usually the OS. You can also seed from
//! another CSPRNG, like [`ThreadRng`], which is faster, but adds another
//! component which must be trusted.
//!
//! ## Not a crypto library
//!
//! When using a CSPRNG for cryptographic purposes, more is required than
//! chosing a good algorithm.
//!
//! It is important not to leak secrets such as the seed or the RNG's internal
//! state, and to prevent other kinds of "side channel attacks". This means
//! among other things that memory needs to be zeroed on move, and should not
//! be written to swap space on disk. Another problem is fork attacks, where
//! the process is forked and each clone generates the same random numbers.
//!
//! This all goes beyond the scope of random number generation, use a good
//! crypto library instead.
//!
//! Rand does take a few precautions however. To avoid printing a CSPRNG's state
//! in log files, implementations have a custom `Debug` implementation which
//! omits internal state. In the future we plan to add some protection against
//! fork attacks.
//!
//! ## Performance
//!
//! Most algorithms don't generate values one at a time, as simple PRNGs, but in
//! blocks. There will be a longer pause when such a block needs to be
//! generated, while a random number can be returned almost instantly when there
//! are unused values in the buffer.
//!
//! Performance may be different depending on the architecture; but in contrast
//! to PRNGs that generate one value at a time, the performance of CSPRNGs
//! rarely if ever depends on the surrounding code.
//!
//! Because generating blocks of values lends itself well to loop unrolling, the
//! code size of CSPRNGs can be significant.
//!
//!
//! # Further reading
//!
//! There is quite a lot that can be said about PRNGs. The [PCG paper] is a
//! very approachable explaining more concepts.
//!
//! A good paper about RNG quality is
//! ["Good random number generators are (not so) easy to find"](
//! http://random.mat.sbg.ac.at/results/peter/A19final.pdf) by P. Hellekalek.
//!
//!
//! [`rngs` module]: ../rngs/index.html
//! [normal PRNGs]: #normal-pseudo-random-number-generators-prngs
//! [CSPRNGs]: #cryptographically-secure-pseudo-random-number-generators-csprngs
//! [`XorShiftRng`]: struct.XorShiftRng.html
//! [`ChaChaRng`]: chacha/struct.ChaChaRng.html
//! [`Hc128Rng`]: hc128/struct.Hc128Rng.html
//! [`IsaacRng`]: isaac/struct.IsaacRng.html
//! [`ThreadRng`]: ../rngs/struct.ThreadRng.html
//! [`FromEntropy`]: ../trait.FromEntropy.html
//! [TestU01]: http://simul.iro.umontreal.ca/testu01/tu01.html
//! [PractRand]: http://pracrand.sourceforge.net/
//! [PCG paper]: http://www.pcg-random.org/pdf/hmc-cs-2014-0905.pdf


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
