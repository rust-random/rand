// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://www.rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The ChaCha random number generator.

use core::fmt;
use {RngCore, CryptoRng, SeedableRng};
use {impls, le};

const SEED_WORDS: usize = 8; // 8 words for the 256-bit key
const STATE_WORDS: usize = 16;

/// A cryptographically secure random number generator that uses the ChaCha
/// algorithm.
///
/// ChaCha is a stream cipher designed by Daniel J. Bernstein [1], that we use
/// as an RNG. It is an improved variant of the Salsa20 cipher family, which was
/// selected as one of the "stream ciphers suitable for widespread adoption" by
/// eSTREAM [2].
///
/// ChaCha uses add-rotate-xor (ARX) operations as its basis. These are safe
/// against timing attacks, although that is mostly a concern for ciphers and
/// not for RNGs. Also it is very suitable for SIMD implementation.
/// Here we do not provide a SIMD implementation yet, except for what is
/// provided by auto-vectorisation.
///
/// With the ChaCha algorithm it is possible to choose the number of rounds the
/// core algorithm should run. By default `ChaChaRng` is created as ChaCha20,
/// which means 20 rounds. The number of rounds is a tradeoff between performance
/// and security, 8 rounds are considered the minimum to be secure. A different
/// number of rounds can be set using [`set_rounds`].
///
/// We deviate slightly from the ChaCha specification regarding the nonce, which
/// is used to extend the counter to 128 bits. This is provably as strong as the
/// original cipher, though, since any distinguishing attack on our variant also
/// works against ChaCha with a chosen-nonce. See the XSalsa20 [3] security
/// proof for a more involved example of this.
///
/// The modified word layout is:
///
/// ```text
/// constant constant constant constant
/// key      key      key      key
/// key      key      key      key
/// counter  counter  counter  counter
/// ```
///
/// [1]: D. J. Bernstein, [*ChaCha, a variant of Salsa20*](
///      https://cr.yp.to/chacha.html)
///
/// [2]: [eSTREAM: the ECRYPT Stream Cipher Project](
///      http://www.ecrypt.eu.org/stream/)
///
/// [3]: Daniel J. Bernstein. [*Extending the Salsa20 nonce.*](
///      http://cr.yp.to/papers.html#xsalsa)
///
/// [`set_rounds`]: #method.set_counter
#[derive(Clone)]
pub struct ChaChaRng {
    buffer:  [u32; STATE_WORDS], // Internal buffer of output
    state:   [u32; STATE_WORDS], // Initial state
    index:   usize,              // Index into state
    rounds:  usize,
}

// Custom Debug implementation that does not expose the internal state
impl fmt::Debug for ChaChaRng {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ChaChaRng {{}}")
    }
}

macro_rules! quarter_round{
    ($a: expr, $b: expr, $c: expr, $d: expr) => {{
        $a = $a.wrapping_add($b); $d ^= $a; $d = $d.rotate_left(16);
        $c = $c.wrapping_add($d); $b ^= $c; $b = $b.rotate_left(12);
        $a = $a.wrapping_add($b); $d ^= $a; $d = $d.rotate_left( 8);
        $c = $c.wrapping_add($d); $b ^= $c; $b = $b.rotate_left( 7);
    }}
}

macro_rules! double_round{
    ($x: expr) => {{
        // Column round
        quarter_round!($x[ 0], $x[ 4], $x[ 8], $x[12]);
        quarter_round!($x[ 1], $x[ 5], $x[ 9], $x[13]);
        quarter_round!($x[ 2], $x[ 6], $x[10], $x[14]);
        quarter_round!($x[ 3], $x[ 7], $x[11], $x[15]);
        // Diagonal round
        quarter_round!($x[ 0], $x[ 5], $x[10], $x[15]);
        quarter_round!($x[ 1], $x[ 6], $x[11], $x[12]);
        quarter_round!($x[ 2], $x[ 7], $x[ 8], $x[13]);
        quarter_round!($x[ 3], $x[ 4], $x[ 9], $x[14]);
    }}
}

impl ChaChaRng {
    /// Create an ChaCha random number generator using the default
    /// fixed key of 8 zero words.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rand::{RngCore, ChaChaRng};
    ///
    /// let mut ra = ChaChaRng::new_unseeded();
    /// println!("{:?}", ra.next_u32());
    /// println!("{:?}", ra.next_u32());
    /// ```
    ///
    /// Since this equivalent to a RNG with a fixed seed, repeated executions
    /// of an unseeded RNG will produce the same result. This code sample will
    /// consistently produce:
    ///
    /// - 2917185654
    /// - 2419978656
    pub fn new_unseeded() -> ChaChaRng {
        ChaChaRng::from_seed([0; SEED_WORDS*4])
    }

    /// Sets the internal 128-bit ChaCha counter to a user-provided value. This
    /// permits jumping arbitrarily ahead (or backwards) in the pseudorandom
    /// stream.
    ///
    /// The 128 bits used for the counter overlap with the nonce and smaller
    /// counter of ChaCha when used as a stream cipher. It is in theory possible
    /// to use `set_counter` to obtain the conventional ChaCha pseudorandom
    /// stream associated with a particular nonce. This is not a supported use
    /// of the RNG, because a nonce set that way is not treated as a constant
    /// value but still as part of the counter, besides endian issues.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rand::{RngCore, ChaChaRng};
    ///
    /// let mut rng1 = ChaChaRng::new_unseeded(); // Use `ChaChaRng::new()` or
    ///                                           // `ChaChaRng::from_rng()`
    ///                                           // outside of testing.
    /// let mut rng2 = rng1.clone();
    ///
    /// // Skip to round 20. Because every round generates 16 `u32` values, this
    /// // actually means skipping 320 values.
    /// for _ in 0..(20*16) { rng1.next_u32(); }
    /// rng2.set_counter(20, 0);
    /// assert_eq!(rng1.next_u32(), rng2.next_u32());
    /// ```
    pub fn set_counter(&mut self, counter_low: u64, counter_high: u64) {
        self.state[12] = counter_low as u32;
        self.state[13] = (counter_low >> 32) as u32;
        self.state[14] = counter_high as u32;
        self.state[15] = (counter_high >> 32) as u32;
        self.index = STATE_WORDS; // force recomputation on next use
    }

    /// Sets the number of rounds to run the ChaCha core algorithm per block to
    /// generate.
    ///
    /// By default this is set to 20. Other recommended values are 12 and 8,
    /// which trade security for performance. `rounds` only supports values
    /// that are multiples of 4 and less than or equal to 20.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rand::{RngCore, ChaChaRng};
    ///
    /// let mut rng = ChaChaRng::new_unseeded(); // Use `ChaChaRng::new()` or
    ///                                           // `ChaChaRng::from_rng()`
    ///                                           // outside of testing.
    /// rng.set_rounds(8);
    ///
    /// assert_eq!(rng.next_u32(), 0x2fef003e);
    /// ```
    pub fn set_rounds(&mut self, rounds: usize) {
        assert!([4usize, 8, 12, 16, 20].iter().any(|x| *x == rounds));
        self.rounds = rounds;
        self.index = STATE_WORDS; // force recomputation on next use
    }

    /// Refill the internal output buffer (`self.buffer`)
    fn update(&mut self) {
        // For some reason extracting this part into a separate function
        // improves performance by 50%.
        fn core(results: &mut [u32; STATE_WORDS],
                state: &[u32; STATE_WORDS],
                rounds: usize)
        {
            let mut tmp = *state;
            for _ in 0..rounds / 2 {
                double_round!(tmp);
            }
            for i in 0..STATE_WORDS {
                results[i] = tmp[i].wrapping_add(state[i]);
            }
        }

        core(&mut self.buffer, &self.state, self.rounds);
        self.index = 0;
        // update 128-bit counter
        self.state[12] = self.state[12].wrapping_add(1);
        if self.state[12] != 0 { return };
        self.state[13] = self.state[13].wrapping_add(1);
        if self.state[13] != 0 { return };
        self.state[14] = self.state[14].wrapping_add(1);
        if self.state[14] != 0 { return };
        self.state[15] = self.state[15].wrapping_add(1);
    }
}

impl RngCore for ChaChaRng {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        // Using a local variable for `index`, and checking the size avoids a
        // bounds check later on.
        let mut index = self.index as usize;
        if index >= STATE_WORDS {
            self.update();
            index = 0;
        }

        let value = self.buffer[index];
        self.index += 1;
        value
    }

    fn next_u64(&mut self) -> u64 {
        impls::next_u64_via_u32(self)
    }


    fn fill_bytes(&mut self, dest: &mut [u8]) {
        let mut read_len = 0;
        while read_len < dest.len() {
            if self.index >= self.buffer.len() {
                self.update();
            }

            let (consumed_u32, filled_u8) =
                impls::fill_via_u32_chunks(&self.buffer[self.index..],
                                           &mut dest[read_len..]);

            self.index += consumed_u32;
            read_len += filled_u8;
        }
    }
}

impl CryptoRng for ChaChaRng {}

impl SeedableRng for ChaChaRng {
    type Seed = [u8; SEED_WORDS*4];
    fn from_seed(seed: Self::Seed) -> Self {
        let mut seed_le = [0u32; SEED_WORDS];
        le::read_u32_into(&seed, &mut seed_le);
        ChaChaRng {
            buffer: [0; STATE_WORDS],
            state: [0x61707865, 0x3320646E, 0x79622D32, 0x6B206574, // constants
                    seed_le[0], seed_le[1], seed_le[2], seed_le[3], // seed
                    seed_le[4], seed_le[5], seed_le[6], seed_le[7], // seed
                    0, 0, 0, 0], // counter
            index: STATE_WORDS, // generate on first use
            rounds: 20,
         }
    }
}

#[cfg(test)]
mod test {
    use {RngCore, SeedableRng};
    use super::ChaChaRng;

    #[test]
    fn test_chacha_construction() {
        let seed = [0,0,0,0,0,0,0,0,
            1,0,0,0,0,0,0,0,
            2,0,0,0,0,0,0,0,
            3,0,0,0,0,0,0,0];
        let mut rng1 = ChaChaRng::from_seed(seed);
        assert_eq!(rng1.next_u32(), 137206642);

        let mut rng2 = ChaChaRng::from_rng(&mut rng1).unwrap();
        assert_eq!(rng2.next_u32(), 1325750369);
    }

    #[test]
    fn test_chacha_true_values_a() {
        // Test vectors 1 and 2 from
        // https://tools.ietf.org/html/draft-nir-cfrg-chacha20-poly1305-04
        let seed = [0u8; 32];
        let mut rng = ChaChaRng::from_seed(seed);

        let mut results = [0u32; 16];
        for i in results.iter_mut() { *i = rng.next_u32(); }
        let expected = [0xade0b876, 0x903df1a0, 0xe56a5d40, 0x28bd8653,
                        0xb819d2bd, 0x1aed8da0, 0xccef36a8, 0xc70d778b,
                        0x7c5941da, 0x8d485751, 0x3fe02477, 0x374ad8b8,
                        0xf4b8436a, 0x1ca11815, 0x69b687c3, 0x8665eeb2];
        assert_eq!(results, expected);

        for i in results.iter_mut() { *i = rng.next_u32(); }
        let expected = [0xbee7079f, 0x7a385155, 0x7c97ba98, 0x0d082d73,
                        0xa0290fcb, 0x6965e348, 0x3e53c612, 0xed7aee32,
                        0x7621b729, 0x434ee69c, 0xb03371d5, 0xd539d874,
                        0x281fed31, 0x45fb0a51, 0x1f0ae1ac, 0x6f4d794b];
        assert_eq!(results, expected);
    }

    #[test]
    fn test_chacha_true_values_b() {
        // Test vector 3 from
        // https://tools.ietf.org/html/draft-nir-cfrg-chacha20-poly1305-04
        let seed = [0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 1];
        let mut rng = ChaChaRng::from_seed(seed);

        // Skip block 0
        for _ in 0..16 { rng.next_u32(); }

        let mut results = [0u32; 16];
        for i in results.iter_mut() { *i = rng.next_u32(); }
        let expected = [0x2452eb3a, 0x9249f8ec, 0x8d829d9b, 0xddd4ceb1,
                        0xe8252083, 0x60818b01, 0xf38422b8, 0x5aaa49c9,
                        0xbb00ca8e, 0xda3ba7b4, 0xc4b592d1, 0xfdf2732f,
                        0x4436274e, 0x2561b3c8, 0xebdd4aa6, 0xa0136c00];
        assert_eq!(results, expected);
    }

    #[test]
    fn test_chacha_true_values_c() {
        // Test vector 4 from
        // https://tools.ietf.org/html/draft-nir-cfrg-chacha20-poly1305-04
        let seed = [0, 0xff, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0];
        let expected = [0xfb4dd572, 0x4bc42ef1, 0xdf922636, 0x327f1394,
                        0xa78dea8f, 0x5e269039, 0xa1bebbc1, 0xcaf09aae,
                        0xa25ab213, 0x48a6b46c, 0x1b9d9bcb, 0x092c5be6,
                        0x546ca624, 0x1bec45d5, 0x87f47473, 0x96f0992e];
        let mut results = [0u32; 16];

        // Test block 2 by skipping block 0 and 1
        let mut rng1 = ChaChaRng::from_seed(seed);
        for _ in 0..32 { rng1.next_u32(); }
        for i in results.iter_mut() { *i = rng1.next_u32(); }
        assert_eq!(results, expected);

        // Test block 2 by using `set_counter`
        let mut rng2 = ChaChaRng::from_seed(seed);
        rng2.set_counter(2, 0);
        for i in results.iter_mut() { *i = rng2.next_u32(); }
        assert_eq!(results, expected);
    }

    #[test]
    fn test_chacha_multiple_blocks() {
        let seed = [0,0,0,0, 1,0,0,0, 2,0,0,0, 3,0,0,0, 4,0,0,0, 5,0,0,0, 6,0,0,0, 7,0,0,0];
        let mut rng = ChaChaRng::from_seed(seed);

        // Store the 17*i-th 32-bit word,
        // i.e., the i-th word of the i-th 16-word block
        let mut results = [0u32; 16];
        for i in results.iter_mut() {
            *i = rng.next_u32();
            for _ in 0..16 {
                rng.next_u32();
            }
        }
        let expected = [0xf225c81a, 0x6ab1be57, 0x04d42951, 0x70858036,
                        0x49884684, 0x64efec72, 0x4be2d186, 0x3615b384,
                        0x11cfa18e, 0xd3c50049, 0x75c775f6, 0x434c6530,
                        0x2c5bad8f, 0x898881dc, 0x5f1c86d9, 0xc1f8e7f4];
        assert_eq!(results, expected);
    }

    #[test]
    fn test_chacha_true_bytes() {
        let seed = [0u8; 32];
        let mut rng = ChaChaRng::from_seed(seed);
        let mut results = [0u8; 32];
        rng.fill_bytes(&mut results);
        let expected = [118, 184, 224, 173, 160, 241, 61, 144,
                        64, 93, 106, 229, 83, 134, 189, 40,
                        189, 210, 25, 184, 160, 141, 237, 26,
                        168, 54, 239, 204, 139, 119, 13, 199];
        assert_eq!(results, expected);
    }

    #[test]
    fn test_chacha_set_counter() {
        // Test vector 5 from
        // https://tools.ietf.org/html/draft-nir-cfrg-chacha20-poly1305-04
        // Although we do not support setting a nonce, we try it here anyway so
        // we can use this test vector.
        let seed = [0u8; 32];
        let mut rng = ChaChaRng::from_seed(seed);
        rng.set_counter(0, 2u64 << 56);

        let mut results = [0u32; 16];
        for i in results.iter_mut() { *i = rng.next_u32(); }
        let expected = [0x374dc6c2, 0x3736d58c, 0xb904e24a, 0xcd3f93ef,
                        0x88228b1a, 0x96a4dfb3, 0x5b76ab72, 0xc727ee54,
                        0x0e0e978a, 0xf3145c95, 0x1b748ea8, 0xf786c297,
                        0x99c28f5f, 0x628314e8, 0x398a19fa, 0x6ded1b53];
        assert_eq!(results, expected);
    }

    #[test]
    fn test_chacha_set_rounds() {
        let seed = [0u8; 32];
        let mut rng = ChaChaRng::from_seed(seed);
        rng.set_rounds(8);

        let mut results = [0u32; 16];
        for i in results.iter_mut() { *i = rng.next_u32(); }

        let expected = [0x2fef003e, 0xd6405f89, 0xe8b85b7f, 0xa1a5091f,
                        0xc30e842c, 0x3b7f9ace, 0x88e11b18, 0x1e1a71ef,
                        0x72e14c98, 0x416f21b9, 0x6753449f, 0x19566d45,
                        0xa3424a31, 0x01b086da, 0xb8fd7b38, 0x42fe0c0e];
        assert_eq!(results, expected);
    }

    #[test]
    fn test_chacha_clone() {
        let seed = [0,0,0,0, 1,0,0,0, 2,0,0,0, 3,0,0,0, 4,0,0,0, 5,0,0,0, 6,0,0,0, 7,0,0,0];
        let mut rng = ChaChaRng::from_seed(seed);
        let mut clone = rng.clone();
        for _ in 0..16 {
            assert_eq!(rng.next_u64(), clone.next_u64());
        }
    }
}
