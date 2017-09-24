// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The ChaCha random number generator.

use core::num::Wrapping as w;
use {Rng, SeedFromRng, SeedableRng, Result};

#[allow(bad_style)]
type w32 = w<u32>;

const KEY_WORDS    : usize =  8; // 8 words for the 256-bit key
const STATE_WORDS  : usize = 16;
const CHACHA_ROUNDS: u32 = 20; // Cryptographically secure from 8 upwards as of this writing

/// A random number generator that uses the ChaCha20 algorithm [1].
///
/// The ChaCha algorithm is widely accepted as suitable for
/// cryptographic purposes, but this implementation has not been
/// verified as such. Prefer a generator like `OsRng` that defers to
/// the operating system for cases that need high security.
///
/// [1]: D. J. Bernstein, [*ChaCha, a variant of
/// Salsa20*](http://cr.yp.to/chacha.html)
#[derive(Copy, Clone, Debug)]
pub struct ChaChaRng {
    buffer:  [w32; STATE_WORDS], // Internal buffer of output
    state:   [w32; STATE_WORDS], // Initial state
    index:   usize,                 // Index into state
}

static EMPTY: ChaChaRng = ChaChaRng {
    buffer:  [w(0); STATE_WORDS],
    state:   [w(0); STATE_WORDS],
    index:   STATE_WORDS
};


macro_rules! quarter_round{
    ($a: expr, $b: expr, $c: expr, $d: expr) => {{
        $a = $a + $b; $d = $d ^ $a; $d = w($d.0.rotate_left(16));
        $c = $c + $d; $b = $b ^ $c; $b = w($b.0.rotate_left(12));
        $a = $a + $b; $d = $d ^ $a; $d = w($d.0.rotate_left( 8));
        $c = $c + $d; $b = $b ^ $c; $b = w($b.0.rotate_left( 7));
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

#[inline]
fn core(output: &mut [w32; STATE_WORDS], input: &[w32; STATE_WORDS]) {
    *output = *input;

    for _ in 0..CHACHA_ROUNDS / 2 {
        double_round!(output);
    }

    for i in 0..STATE_WORDS {
        output[i] = output[i] + input[i];
    }
}

impl ChaChaRng {
    /// Create an ChaCha random number generator using the default
    /// fixed key of 8 zero words.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rand::Rng;
    /// use rand::prng::ChaChaRng;
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
        let mut rng = EMPTY;
        rng.init(&[0; KEY_WORDS]);
        rng
    }

    /// Sets the internal 128-bit ChaCha counter to
    /// a user-provided value. This permits jumping
    /// arbitrarily ahead (or backwards) in the pseudorandom stream.
    ///
    /// Since the nonce words are used to extend the counter to 128 bits,
    /// users wishing to obtain the conventional ChaCha pseudorandom stream
    /// associated with a particular nonce can call this function with
    /// arguments `0, desired_nonce`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rand::Rng;
    /// use rand::prng::ChaChaRng;
    ///
    /// let mut ra = ChaChaRng::new_unseeded();
    /// ra.set_counter(0u64, 1234567890u64);
    /// println!("{:?}", ra.next_u32());
    /// println!("{:?}", ra.next_u32());
    /// ```
    pub fn set_counter(&mut self, counter_low: u64, counter_high: u64) {
        self.state[12] = w((counter_low >>  0) as u32);
        self.state[13] = w((counter_low >> 32) as u32);
        self.state[14] = w((counter_high >>  0) as u32);
        self.state[15] = w((counter_high >> 32) as u32);
        self.index = STATE_WORDS; // force recomputation
    }

    /// Initializes `self.state` with the appropriate key and constants
    ///
    /// We deviate slightly from the ChaCha specification regarding
    /// the nonce, which is used to extend the counter to 128 bits.
    /// This is provably as strong as the original cipher, though,
    /// since any distinguishing attack on our variant also works
    /// against ChaCha with a chosen-nonce. See the XSalsa20 [1]
    /// security proof for a more involved example of this.
    ///
    /// The modified word layout is:
    /// ```text
    /// constant constant constant constant
    /// key      key      key      key
    /// key      key      key      key
    /// counter  counter  counter  counter
    /// ```
    /// [1]: Daniel J. Bernstein. [*Extending the Salsa20
    /// nonce.*](http://cr.yp.to/papers.html#xsalsa)
    fn init(&mut self, key: &[u32; KEY_WORDS]) {
        self.state[0] = w(0x61707865);
        self.state[1] = w(0x3320646E);
        self.state[2] = w(0x79622D32);
        self.state[3] = w(0x6B206574);

        for i in 0..KEY_WORDS {
            self.state[4+i] = w(key[i]);
        }

        self.state[12] = w(0);
        self.state[13] = w(0);
        self.state[14] = w(0);
        self.state[15] = w(0);

        self.index = STATE_WORDS;
    }

    /// Refill the internal output buffer (`self.buffer`)
    fn update(&mut self) {
        core(&mut self.buffer, &self.state);
        self.index = 0;
        // update 128-bit counter
        self.state[12] = self.state[12] + w(1);
        if self.state[12] != w(0) { return };
        self.state[13] = self.state[13] + w(1);
        if self.state[13] != w(0) { return };
        self.state[14] = self.state[14] + w(1);
        if self.state[14] != w(0) { return };
        self.state[15] = self.state[15] + w(1);
    }
}

impl Rng for ChaChaRng {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        if self.index == STATE_WORDS {
            self.update();
        }

        let value = self.buffer[self.index % STATE_WORDS];
        self.index += 1;
        value.0
    }
    
    fn next_u64(&mut self) -> u64 {
        ::rand_core::impls::next_u64_via_u32(self)
    }
    #[cfg(feature = "i128_support")]
    fn next_u128(&mut self) -> u128 {
        ::rand_core::impls::next_u128_via_u64(self)
    }
    
    // Custom implementation allowing larger reads from buffer is about 8%
    // faster than default implementation in my tests
    fn try_fill(&mut self, dest: &mut [u8]) -> Result<()> {
        use core::cmp::min;
        use core::intrinsics::{transmute, copy_nonoverlapping};
        
        let mut left = dest;
        while left.len() >= 4 {
            if self.index == STATE_WORDS {
                self.update();
            }
            
            let words = min(left.len() / 4, STATE_WORDS - self.index);
            let (l, r) = {left}.split_at_mut(4 * words);
            left = r;
            
            // convert to LE:
            for ref mut x in self.buffer[self.index..self.index+words].iter_mut() {
                **x = w((*x).0.to_le());
            }
            
            unsafe{ copy_nonoverlapping(
                &self.buffer[self.index].0 as *const u32 as *const u8,
                l.as_mut_ptr(),
                words) };
            self.index += words;
        }
        let n = left.len();
        if n > 0 {
            let chunk: [u8; 4] = unsafe {
                transmute(self.next_u32().to_le())
            };
            left.copy_from_slice(&chunk[..n]);
        }
        Ok(())
    }
}

impl SeedFromRng for ChaChaRng {
    fn from_rng<R: Rng+?Sized>(other: &mut R) -> Result<Self> {
        let mut key : [u32; KEY_WORDS] = [0; KEY_WORDS];
        for word in key.iter_mut() {
            *word = other.next_u32();
        }
        Ok(SeedableRng::from_seed(&key[..]))
    }
}

impl<'a> SeedableRng<&'a [u32]> for ChaChaRng {
    /// Create a ChaCha generator from a seed,
    /// obtained from a variable-length u32 array.
    /// Only up to 8 words are used; if less than 8
    /// words are used, the remaining are set to zero.
    fn from_seed(seed: &'a [u32]) -> ChaChaRng {
        let mut rng = EMPTY;
        rng.init(&[0u32; KEY_WORDS]);
        // set key in place
        {
            let key = &mut rng.state[4 .. 4+KEY_WORDS];
            for (k, s) in key.iter_mut().zip(seed.iter()) {
                *k = w(*s);
            }
        }
        rng
    }
}


#[cfg(test)]
mod test {
    use {Rng, SeedableRng, iter};
    use distributions::ascii_word_char;
    use super::ChaChaRng;

    #[test]
    fn test_rng_rand_seeded() {
        let s = iter(&mut ::test::rng()).map(|rng| rng.next_u32()).take(8).collect::<Vec<u32>>();
        let mut ra: ChaChaRng = SeedableRng::from_seed(&s[..]);
        let mut rb: ChaChaRng = SeedableRng::from_seed(&s[..]);
        assert!(::test::iter_eq(iter(&mut ra).map(|rng| ascii_word_char(rng)).take(100),
                                iter(&mut rb).map(|rng| ascii_word_char(rng)).take(100)));
    }

    #[test]
    fn test_rng_seeded() {
        let seed : &[_] = &[0,1,2,3,4,5,6,7];
        let mut ra: ChaChaRng = SeedableRng::from_seed(seed);
        let mut rb: ChaChaRng = SeedableRng::from_seed(seed);
        assert!(::test::iter_eq(iter(&mut ra).map(|rng| ascii_word_char(rng)).take(100),
                                iter(&mut rb).map(|rng| ascii_word_char(rng)).take(100)));
    }

    #[test]
    fn test_rng_true_values() {
        // Test vectors 1 and 2 from
        // http://tools.ietf.org/html/draft-nir-cfrg-chacha20-poly1305-04
        let seed : &[_] = &[0u32; 8];
        let mut ra: ChaChaRng = SeedableRng::from_seed(seed);

        let v = (0..16).map(|_| ra.next_u32()).collect::<Vec<_>>();
        assert_eq!(v,
                   vec!(0xade0b876, 0x903df1a0, 0xe56a5d40, 0x28bd8653,
                        0xb819d2bd, 0x1aed8da0, 0xccef36a8, 0xc70d778b,
                        0x7c5941da, 0x8d485751, 0x3fe02477, 0x374ad8b8,
                        0xf4b8436a, 0x1ca11815, 0x69b687c3, 0x8665eeb2));

        let v = (0..16).map(|_| ra.next_u32()).collect::<Vec<_>>();
        assert_eq!(v,
                   vec!(0xbee7079f, 0x7a385155, 0x7c97ba98, 0x0d082d73,
                        0xa0290fcb, 0x6965e348, 0x3e53c612, 0xed7aee32,
                        0x7621b729, 0x434ee69c, 0xb03371d5, 0xd539d874,
                        0x281fed31, 0x45fb0a51, 0x1f0ae1ac, 0x6f4d794b));


        let seed : &[_] = &[0,1,2,3,4,5,6,7];
        let mut ra: ChaChaRng = SeedableRng::from_seed(seed);

        // Store the 17*i-th 32-bit word,
        // i.e., the i-th word of the i-th 16-word block
        let mut v : Vec<u32> = Vec::new();
        for _ in 0..16 {
            v.push(ra.next_u32());
            for _ in 0..16 {
                ra.next_u32();
            }
        }

        assert_eq!(v,
                   vec!(0xf225c81a, 0x6ab1be57, 0x04d42951, 0x70858036,
                        0x49884684, 0x64efec72, 0x4be2d186, 0x3615b384,
                        0x11cfa18e, 0xd3c50049, 0x75c775f6, 0x434c6530,
                        0x2c5bad8f, 0x898881dc, 0x5f1c86d9, 0xc1f8e7f4));
    }

    #[test]
    fn test_rng_clone() {
        let seed : &[_] = &[0u32; 8];
        let mut rng: ChaChaRng = SeedableRng::from_seed(seed);
        let mut clone = rng.clone();
        for _ in 0..16 {
            assert_eq!(rng.next_u64(), clone.next_u64());
        }
    }
}
