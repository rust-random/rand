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
//! - [basic PRNGs], primarily designed for simulations
//! - [CSPRNGs], primarily designed for cryptography
//!
//! In simple terms, the basic PRNGs are often predictable; CSPRNGs should not
//! be predictable *when used correctly*.
//! 
//! Contents of this documentation:
//!
//! 1. [The generators](#the-generators)
//! 1. [Performance and size](#performance)
//! 1. [Quality and cycle length](#quality)
//! 1. [Security](#security)
//! 1. [Extra features](#extra-features)
//! 1. [Further reading](#further-reading)
//!
//!
//! # The generators
//!
//! ## Basic pseudo-random number generators (PRNGs)
//!
//! The goal of non-cryptographic PRNGs is usually to find a good balance between
//! simplicity, quality, memory usage and performance. These algorithms are
//! very important to Monte Carlo simulations, and also suitable for several
//! other problems such as randomised algorithms and games (except where there
//! is a risk of players predicting the next output value from previous values,
//! in which case a CSPRNG should be used).
//!
//! Currently Rand provides only one PRNG, and not a very good one at that:
//!
//! | name | performance | worst-case | memory usage | initialisation | quality | predictability |
//! |----- |------------ |----------- | -------------|--------------- |-------- |--------------- |
//! | [`XorShiftRng`] | fast | fast | 16 bytes | fast | poor | trivial after 4 words |
//!
//! ## Cryptographically secure pseudo-random number generators (CSPRNGs)
//!
//! CSPRNGs have much higher requirements than normal PRNGs. The primary
//! consideration is security. Performance and simplicity are also important,
//! but in general CSPRNGs are more complex and slower than normal PRNGs.
//! Quality is no longer a concern, as it is a requirement for a
//! CSPRNG that the output is basically indistinguishable from true randomness
//! since any bias or correlation makes the output more predictable.
//!
//! There is a close relationship between CSPRNGs and cryptographic ciphers.
//! Any block cipher can be turned into a CSPRNG simply by encrypting a counter.
//! Stream ciphers are simply a CSPRNG and a combining operation, usually XOR.
//! This means that we can easily use any stream cipher as a CSPRNG.
//!
//! Rand currently provides two trustworthy CSPRNGs and two CSPRNG-like PRNGs:
//!
//! | name | performance | memory usage | initialisation | predictability | forward-secure |
//! |----- |------------ | -------------|--------------- |--------------- |--------------- |
//! | [`ChaChaRng`] | moderate | 136 bytes | fast        | secure         | no             |
//! | [`Hc128Rng`] | fast | 4176 bytes  | slow           | secure         | no             |
//! | [`IsaacRng`] | good | 2072 bytes  | slow           | unknown        | unknown        |
//! | [`Isaac64Rng`] | fast | 4136 bytes | slow          | unknown        | unknown        |
//!
//! It should be noted that the ISAAC generators are only included for
//! historical reasons, originally being selected as a "compromise" between
//! security and performance. They have good quality output and no attacks are
//! known, but have received little review from cryptography experts.
//!
//!
//! # Performance
//!
//! First it has to be said most PRNGs are very fast, and will
//! rarely be a performance bottleneck. Performance of PRNGs is however a bit of
//! a subtle thing. It depends a lot on the CPU architecture (32 vs. 64 bits),
//! inlining, and also on the number available of registers. The performance of
//! simple PRNGs is often affected by surrounding code due to inlining and
//! other usage of registers.
//!
//! When choosing a PRNG for performance it is very important to benchmark your
//! own application due to interactions between PRNGs and surrounding code and
//! dependence on the CPU architecture as well as the impact of the size of
//! data requested. Because of all this, we do not include performance numbers
//! here but merely a qualitative description.
//!
//! CSPRNGs are a little different in that they typically generate a block of
//! output in a cache, and pull outputs from the cache. This allows them to have
//! good amortised performance, and reduces or completely removes the influence
//! of surrounding code on the CSPRNG performance.
//!
//! ## Worst-case performance
//!
//! Simple PRNGs tend to use constant-time functions and thus have very good
//! worst case performance. In contrast, CSPRNGs usually produce a block of
//! values into a cache, giving them poor worst case performance.
//!
//! ## State size
//!
//! Simple PRNGs often use very little memory, from as little as one word but
//! commonly 2-4 words, where a *word* is usually either `u32` or `u64`. This
//! is not universal across non-cryptographic PRNGs however; for example the
//! previously popular Mersenne Twister MT19937 algorithm requires 2.5 kB of
//! state.
//!
//! CSPRNGs typically require more memory; since the seed size is recommended
//! to be at least 192 bits and more memory is required for a counter, 256 bits
//! would be approximately the minimum secure size. In practice, CSPRNGs tend
//! to use a lot of memory; [`ChaChaRng`] is relatively small with 512 bits
//! state + 512 bits cache + cache counter (136 bytes on x86_64) while [`Hc128Rng`]
//! requires over 4 kB.
//! 
//! ## Initialisation time
//!
//! The time required to initialise new generators varies significantly. Many
//! simple PRNGs and even some cryptographic ones (including [`ChaChaRng`])
//! only need to copy the seed value and some constants into their state, and
//! thus can be constructed very quickly. In contrast, CSPRNGs with large state
//! require key-expansion, often achieved by using their state-advance function
//! many times over.
//!
//! # Quality
//!
//! PRNGs are based in mathematical Number Theory. The quality of PRNG
//! algorithms can be evaluated both analytically and empirically in order to
//! examine for bias, correlations and cycle length.
//!
//! Many simple PRNGs are not much more than a couple of bitwise and arithmetic
//! operations. Their simplicity gives good performance, but also means there
//! are small regularities hidden in the generated random number stream.
//!
//! How much do those hidden regularities matter? That is hard to say, and
//! depends on how the RNG gets used. If there happen to be correlations between
//! the random numbers and the algorithm they are used in, the results can be
//! wrong or misleading.
//!
//! CSPRNGs tend to be much more complex (or at least use many more operations)
//! and have an explicit requirement to be unpredictable; this implies there
//! must be no obvious correlations between output values.
//!
//! A random number generator can be considered good if it gives the correct
//! results in as many applications as possible. There are test suites designed
//! to test how well a PRNG performs on a wide range of possible uses, the
//! latest and most complete of which are [TestU01] and [PractRand].
//!
//! ## Period
//!
//! The *period* or *cycle length* of a PRNG is the number of samples (or amount
//! of data) which can be generated before the algorithm's state returns to a
//! previous value (from where it will *cycle* over all previous output again).
//! Since PRNGs typically have a fixed state size, the maximum cycle length is
//! 2<sup>n</sup> where *n* is the number of bits in the state, but often it is
//! less; with some algorithms the cycle length is fixed, while for others it
//! depends on the seed.
//!
//! Generally it is desired that the cycle length is sufficiently long not to
//! cycle during usage; a period of *only* 2<sup>64</sup> can be used for
//! centuries before cycling. Despite this, we recommend a period of
//! 2<sup>128</sup> or more, which most modern PRNGs satisfy; alternatively
//! a PRNG with shorter period but support for multiple streams may be chosen.
//! There are two reasons for this, as follows.
//!
//! With small PRNGs, often two different seeds will be part of the same cycle,
//! thus will use two slices from the same (large) sequence. There is no
//! guarantee that these slices do not overlap, although when the whole sequence
//! (cycle) is much larger than the slices the chance of overlap is small.
//! When many independently seeded PRNGs are used this is especially important.
//!
//! If the period of the RNG is 2<sup>128</sup>, and an application consumes
//! 2<sup>48</sup> values, it then takes about 2<sup>32</sup> random
//! initializations to have a chance of 1 in a million to repeat part of an
//! already used stream. This seems good enough for common usage of
//! non-cryptographic generators, hence the recommendation of at least
//! 2<sup>128</sup>. As an estimate, the chance of any overlap in a period of
//! size `p` with `n` independent seeds and `u` values used per seed is
//! approximately `1 - e^(-u * n^2 / (2 * p))`.
//!
//! Further, it is not recommended to use the full period of an RNG. Many
//! PRNGs have a property called *k-dimensional equidistribution*, meaning that
//! for values of some size (potentially larger than the output size), all
//! possible values are produced the same number of times over the generator's
//! period. This is not a property of true randomness. This is known as the
//! generalized birthday problem, see the [PCG paper] for a good explanation.
//! This results in a noticable bias on output after generating more values
//! than the square root of the period (after 2<sup>64</sup> values for a
//! period of 2<sup>128</sup>).
//!
//!
//! # Security
//!
//! ## Predictability
//!
//! From the context of any PRNG, one can ask the question *given some previous
//! output from the PRNG, is it possible to predict the next output value?*
//!
//! Simple PRNGs tend to fall into one of two categories here; *yes* and
//! *possibly*. In some cases prediction is trivial; e.g. plain Xorshift outputs
//! part of its state without mutation, and prediction is as simple as seeding
//! a new Xorshift generator from four `u32` outputs. The widely-used Mersenne
//! Twister algorithms are also easy to predict, though more samples are
//! required (624 `u32` samples, in the case of MT19937). At the other end of
//! the range, the PCG generators are small and fast yet designed to be
//! [hard to predict](http://www.pcg-random.org/predictability.html),
//! however they should not be trusted to be secure.
//!
//! The basic security that CSPRNGs must provide is precisely the above, i.e.
//! infeasible to predict. This requirement is formalised as the
//! [next-bit test]; this is roughly stated as: given the first *k* bits of a
//! random sequence, the sequence satisfies the next-bit test if there is no
//! algorithm able to predict the next bit using reasonable computing power.
//! We therefore rate predictability as one of *secure*, *unknown* (meaning
//! apparently strong and no known attacks, but not trusted) or *insecure*.
//!
//! A further security that *some* CSPRNGs provide is forward-security: in the
//! event that the CSPRNGs state is revealed after generating some output, it
//! must be infeasible to reconstruct previous states or output. Note that many
//! CSPRNGs *do not* have forward-security in their usual formulations. It is
//! possible to make any CSPRNG forward-secure by reseeding it from its own
//! output after generating each output value, however this is quite slow
//! (especially since CSPRNGs usually cache a block of output values).
//!
//! As an outsider it is hard to get a good idea about the security of an
//! algorithm. People in the field of cryptography spend a lot of effort
//! analyzing existing designs, and what was once considered good may now turn
//! out to be weaker. Generally it is best to use algorithms well-analyzed by
//! experts, such as those recommended by NIST or ECRYPT.
//!
//! ## State and seeding
//!
//! It is worth noting that a CSPRNG's security relies absolutely on being
//! seeded with a secure random key. Should the key be known or guessable, all
//! output of the CSPRNG is easy to guess. This implies that the seed should
//! come from a trusted source; usually either the OS or another CSPRNG. Our
//! seeding helper trait, [`FromEntropy`], and the source it uses
//! ([`EntropyRng`]), should be secure. Additionally, [`ThreadRng`] is a CSPRNG,
//! thus it is acceptable to seed from this (although for security applications
//! fresh/external entropy should be preferred).
//!
//! Further, it should be obvious that the internal state of a CSPRNG must be
//! kept secret. With that in mind, our implementations do not provide direct
//! access to most of their internal state, and `Debug` implementations do not
//! print any internal state. Of course this does not fully protect CSPRNG
//! state; code within the same process may of course read this memory (and we
//! allow cloning and serialisation of CSPRNGs for convenience). Further, a
//! running process may be forked by the operating system, which may leave both
//! processes with a copy of the same generator.
//!
//! ## Not a crypto library
//!
//! It should be emphasised that this is not a cryptography library; although
//! Rand does take some measures to provide secure random numbers, it does not
//! necessarily take all recommended measures. Further, cryptographic processes
//! such as encryption and authentication are complex and must be implemented
//! very carefully to avoid flaws and resist known attacks. It is therefore
//! recommended to use a higher-level libraries where possible, for example
//! [openssl], [ring] and the [RustCrypto libraries].
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
//! # Extra features
//!
//! Some PRNGs may provide extra features:
//!
//! - Support for multiple streams, which can help with parallel tasks
//! - The ability to jump or seek around in the random number stream;
//!   with large periood this can be used as an alternative to streams
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
//! [basic PRNGs]: #basic-pseudo-random-number-generators-prngs
//! [CSPRNGs]: #cryptographically-secure-pseudo-random-number-generators-csprngs
//! [`XorShiftRng`]: struct.XorShiftRng.html
//! [`ChaChaRng`]: chacha/struct.ChaChaRng.html
//! [`Hc128Rng`]: hc128/struct.Hc128Rng.html
//! [`IsaacRng`]: isaac/struct.IsaacRng.html
//! [`Isaac64Rng`]: isaac64/struct.Isaac64Rng.html
//! [`ThreadRng`]: ../rngs/struct.ThreadRng.html
//! [`FromEntropy`]: ../trait.FromEntropy.html
//! [TestU01]: http://simul.iro.umontreal.ca/testu01/tu01.html
//! [PractRand]: http://pracrand.sourceforge.net/
//! [PCG paper]: http://www.pcg-random.org/pdf/hmc-cs-2014-0905.pdf
//! [openssl]: https://crates.io/crates/openssl
//! [ring]: https://crates.io/crates/ring
//! [RustCrypto libraries]: https://github.com/RustCrypto


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
