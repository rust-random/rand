// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The ISAAC random number generator.

use core::{fmt, slice};
use core::num::Wrapping as w;

use {RngCore, SeedableRng, Error};
use {impls, le};

#[allow(non_camel_case_types)]
type w32 = w<u32>;

const RAND_SIZE_LEN: usize = 8;
const RAND_SIZE: usize = 1 << RAND_SIZE_LEN;

/// A random number generator that uses the ISAAC algorithm.
///
/// ISAAC stands for "Indirection, Shift, Accumulate, Add, and Count" which are
/// the principal bitwise operations employed. It is the most advanced of a
/// series of array based random number generator designed by Robert Jenkins
/// in 1996[1][2].
///
/// Although ISAAC is designed to be cryptographically secure, its design is not
/// founded in cryptographic theory. Therefore it is _not recommended for_
/// cryptographic purposes. It is however one of the strongest non-cryptograpic
/// RNGs, and that while still being reasonably fast.
///
/// Where fast random numbers are needed which should still be secure, but where
/// speed is more important than absolute (cryptographic) security (e.g. to
/// initialise hashes in the std library), a generator like ISAAC may be a good
/// choice.
///
/// In 2006 an improvement to ISAAC was suggested by Jean-Philippe Aumasson,
/// named ISAAC+[3]. But because the specification is not complete, there is no
/// good implementation, and because the suggested bias may not exist, it is not
/// implemented here.
///
/// ## Overview of the ISAAC algorithm:
/// (in pseudo-code)
///
/// ```text
/// Input: a, b, c, s[256] // state
/// Output: r[256]         // results
///
/// mix(a,i) = a ^ a << 13   if i = 0 mod 4
///            a ^ a >>  6   if i = 1 mod 4
///            a ^ a <<  2   if i = 2 mod 4
///            a ^ a >> 16   if i = 3 mod 4
///
/// c = c + 1
/// b = b + c
///
/// for i in 0..256 {
///     x = s_[i]
///     a = f(a,i) + s[i+128 mod 256]
///     y = a + b + s[x>>2 mod 256]
///     s[i] = y
///     b = x + s[y>>10 mod 256]
///     r[i] = b
/// }
/// ```
///
/// Numbers are generated in blocks of 256. This means the function above only
/// runs once every 256 times you ask for a next random number. In all other
/// circumstances the last element of the results array is returned.
///
/// ISAAC therefore needs a lot of memory, relative to other non-vrypto RNGs.
/// 2 * 256 * 4 = 2 kb to hold the state and results.
///
/// ## References
/// [1]: Bob Jenkins, [*ISAAC: A fast cryptographic random number generator*](
///      http://burtleburtle.net/bob/rand/isaacafa.html)
///
/// [2]: Bob Jenkins, [*ISAAC and RC4*](
///      http://burtleburtle.net/bob/rand/isaac.html)
///
/// [3]: Jean-Philippe Aumasson, [*On the pseudo-random generator ISAAC*](
///      https://eprint.iacr.org/2006/438)
#[cfg_attr(feature="serde-1", derive(Serialize,Deserialize))]
pub struct IsaacRng {
    #[cfg_attr(feature="serde-1",serde(with="super::isaac_serde::rand_size_serde"))]
    rsl: [u32; RAND_SIZE],
    #[cfg_attr(feature="serde-1",serde(with="super::isaac_serde::rand_size_serde"))]
    mem: [w32; RAND_SIZE],
    a: w32,
    b: w32,
    c: w32,
    index: u32,
}

// Cannot be derived because [u32; 256] does not implement Clone
// FIXME: remove once RFC 2000 gets implemented
impl Clone for IsaacRng {
    fn clone(&self) -> IsaacRng {
        IsaacRng {
            rsl: self.rsl,
            mem: self.mem,
            a: self.a,
            b: self.b,
            c: self.c,
            index: self.index,
        }
    }
}

// Custom Debug implementation that does not expose the internal state
impl fmt::Debug for IsaacRng {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "IsaacRng {{}}")
    }
}

impl IsaacRng {
    /// Create an ISAAC random number generator using the default
    /// fixed seed.
    pub fn new_unseeded() -> IsaacRng {
        Self::new_from_u64(0)
    }

    /// Creates an ISAAC random number generator using an u64 as seed.
    /// If `seed == 0` this will produce the same stream of random numbers as
    /// the reference implementation when used unseeded.
    pub fn new_from_u64(seed: u64) -> IsaacRng {
        let mut key = [w(0); RAND_SIZE];
        key[0] = w(seed as u32);
        key[1] = w((seed >> 32) as u32);
        // Initialize with only one pass.
        // A second pass does not improve the quality here, because all of
        // the seed was already available in the first round.
        // Not doing the second pass has the small advantage that if `seed == 0`
        // this method produces exactly the same state as the reference
        // implementation when used unseeded.
        init(key, 1)
    }

    /// Refills the output buffer (`self.rsl`)
    /// See also the pseudocode desciption of the algorithm at the top of this
    /// file.
    ///
    /// Optimisations used (similar to the reference implementation):
    /// - The loop is unrolled 4 times, once for every constant of mix().
    /// - The contents of the main loop are moved to a function `rngstep`, to
    ///   reduce code duplication.
    /// - We use local variables for a and b, which helps with optimisations.
    /// - We split the main loop in two, one that operates over 0..128 and one
    ///   over 128..256. This way we can optimise out the addition and modulus
    ///   from `s[i+128 mod 256]`.
    /// - We maintain one index `i` and add `m` or `m2` as base (m2 for the
    ///   `s[i+128 mod 256]`), relying on the optimizer to turn it into pointer
    ///   arithmetic.
    /// - We fill `rsl` backwards. The reference implementation reads values
    ///   from `rsl` in reverse. We read them in the normal direction, to make
    ///   `fill_bytes` a memcopy. To maintain compatibility we fill in reverse.
    fn isaac(&mut self) {
        self.c += w(1);
        // abbreviations
        let mut a = self.a;
        let mut b = self.b + self.c;
        const MIDPOINT: usize = RAND_SIZE / 2;

        #[inline]
        fn ind(mem:&[w32; RAND_SIZE], v: w32, amount: usize) -> w32 {
            let index = (v >> amount).0 as usize % RAND_SIZE;
            mem[index]
        }

        #[inline]
        fn rngstep(ctx: &mut IsaacRng,
                   mix: w32,
                   a: &mut w32,
                   b: &mut w32,
                   base: usize,
                   m: usize,
                   m2: usize) {
            let x = ctx.mem[base + m];
            *a = mix + ctx.mem[base + m2];
            let y = *a + *b + ind(&ctx.mem, x, 2);
            ctx.mem[base + m] = y;
            *b = x + ind(&ctx.mem, y, 2 + RAND_SIZE_LEN);
            ctx.rsl[RAND_SIZE - 1 - base - m] = (*b).0;
        }

        let mut m = 0;
        let mut m2 = MIDPOINT;
        for i in (0..MIDPOINT/4).map(|i| i * 4) {
            rngstep(self, a ^ (a << 13), &mut a, &mut b, i + 0, m, m2);
            rngstep(self, a ^ (a >> 6 ),  &mut a, &mut b, i + 1, m, m2);
            rngstep(self, a ^ (a << 2 ),  &mut a, &mut b, i + 2, m, m2);
            rngstep(self, a ^ (a >> 16),  &mut a, &mut b, i + 3, m, m2);
        }

        m = MIDPOINT;
        m2 = 0;
        for i in (0..MIDPOINT/4).map(|i| i * 4) {
            rngstep(self, a ^ (a << 13), &mut a, &mut b, i + 0, m, m2);
            rngstep(self, a ^ (a >> 6 ),  &mut a, &mut b, i + 1, m, m2);
            rngstep(self, a ^ (a << 2 ),  &mut a, &mut b, i + 2, m, m2);
            rngstep(self, a ^ (a >> 16),  &mut a, &mut b, i + 3, m, m2);
        }

        self.a = a;
        self.b = b;
        self.index = 0;
    }
}

impl RngCore for IsaacRng {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        // Using a local variable for `index`, and checking the size avoids a
        // bounds check later on.
        let mut index = self.index as usize;
        if index >= RAND_SIZE {
            self.isaac();
            index = 0;
        }

        let value = self.rsl[index];
        self.index += 1;
        value
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        impls::next_u64_via_u32(self)
    }


    fn fill_bytes(&mut self, dest: &mut [u8]) {
        let mut read_len = 0;
        while read_len < dest.len() {
            if self.index as usize >= RAND_SIZE {
                self.isaac();
            }

            let (consumed_u32, filled_u8) =
                impls::fill_via_u32_chunks(&self.rsl[(self.index as usize)..],
                                           &mut dest[read_len..]);

            self.index += consumed_u32 as u32;
            read_len += filled_u8;
        }
    }
}

/// Creates a new ISAAC random number generator.
///
/// The author Bob Jenkins describes how to best initialize ISAAC here:
/// https://rt.cpan.org/Public/Bug/Display.html?id=64324
/// The answer is included here just in case:
///
/// "No, you don't need a full 8192 bits of seed data. Normal key sizes will do
/// fine, and they should have their expected strength (eg a 40-bit key will
/// take as much time to brute force as 40-bit keys usually will). You could
/// fill the remainder with 0, but set the last array element to the length of
/// the key provided (to distinguish keys that differ only by different amounts
/// of 0 padding). You do still need to call randinit() to make sure the initial
/// state isn't uniform-looking."
/// "After publishing ISAAC, I wanted to limit the key to half the size of r[],
/// and repeat it twice. That would have made it hard to provide a key that sets
/// the whole internal state to anything convenient. But I'd already published
/// it."
///
/// And his answer to the question "For my code, would repeating the key over
/// and over to fill 256 integers be a better solution than zero-filling, or
/// would they essentially be the same?":
/// "If the seed is under 32 bytes, they're essentially the same, otherwise
/// repeating the seed would be stronger. randinit() takes a chunk of 32 bytes,
/// mixes it, and combines that with the next 32 bytes, et cetera. Then loops
/// over all the elements the same way a second time."
#[inline]
fn init(mut mem: [w32; RAND_SIZE], rounds: u32) -> IsaacRng {
    // These numbers are the result of initializing a...h with the
    // fractional part of the golden ratio in binary (0x9e3779b9)
    // and applying mix() 4 times.
    let mut a = w(0x1367df5a);
    let mut b = w(0x95d90059);
    let mut c = w(0xc3163e4b);
    let mut d = w(0x0f421ad8);
    let mut e = w(0xd92a4a78);
    let mut f = w(0xa51a3c49);
    let mut g = w(0xc4efea1b);
    let mut h = w(0x30609119);

    // Normally this should do two passes, to make all of the seed effect all
    // of `mem`
    for _ in 0..rounds {
        for i in (0..RAND_SIZE/8).map(|i| i * 8) {
            a += mem[i  ]; b += mem[i+1];
            c += mem[i+2]; d += mem[i+3];
            e += mem[i+4]; f += mem[i+5];
            g += mem[i+6]; h += mem[i+7];
            mix(&mut a, &mut b, &mut c, &mut d,
                &mut e, &mut f, &mut g, &mut h);
            mem[i  ] = a; mem[i+1] = b;
            mem[i+2] = c; mem[i+3] = d;
            mem[i+4] = e; mem[i+5] = f;
            mem[i+6] = g; mem[i+7] = h;
        }
    }

    let mut rng = IsaacRng {
        rsl: [0; RAND_SIZE],
        mem: mem,
        a: w(0),
        b: w(0),
        c: w(0),
        index: 0,
    };

    // Prepare the first set of results
    rng.isaac();
    rng
}

fn mix(a: &mut w32, b: &mut w32, c: &mut w32, d: &mut w32,
       e: &mut w32, f: &mut w32, g: &mut w32, h: &mut w32) {
    *a ^= *b << 11; *d += *a; *b += *c;
    *b ^= *c >> 2;  *e += *b; *c += *d;
    *c ^= *d << 8;  *f += *c; *d += *e;
    *d ^= *e >> 16; *g += *d; *e += *f;
    *e ^= *f << 10; *h += *e; *f += *g;
    *f ^= *g >> 4;  *a += *f; *g += *h;
    *g ^= *h << 8;  *b += *g; *h += *a;
    *h ^= *a >> 9;  *c += *h; *a += *b;
}

impl SeedableRng for IsaacRng {
    type Seed = [u8; 32];

    fn from_seed(seed: Self::Seed) -> Self {
        let mut seed_u32 = [0u32; 8];
        le::read_u32_into(&seed, &mut seed_u32);
        let mut seed_extended = [w(0); RAND_SIZE];
        for (x, y) in seed_extended.iter_mut().zip(seed_u32.iter()) {
            *x = w(*y);
        }
        init(seed_extended, 2)
    }

    fn from_rng<R: RngCore>(rng: &mut R) -> Result<Self, Error> {
        // Custom `from_rng` implementation that fills a seed with the same size
        // as the entire state.
        let mut seed = [w(0u32); RAND_SIZE];
        unsafe {
            let ptr = seed.as_mut_ptr() as *mut u8;

            let slice = slice::from_raw_parts_mut(ptr, RAND_SIZE * 4);
            rng.try_fill_bytes(slice)?;
        }
        for i in seed.iter_mut() {
            *i = w(i.0.to_le());
        }

        Ok(init(seed, 2))
    }
}

#[cfg(test)]
mod test {
    use {RngCore, SeedableRng};
    use super::IsaacRng;

    #[test]
    fn test_isaac_construction() {
        // Test that various construction techniques produce a working RNG.
        let seed = [1,0,0,0, 23,0,0,0, 200,1,0,0, 210,30,0,0,
                    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
        let mut rng1 = IsaacRng::from_seed(seed);
        assert_eq!(rng1.next_u32(), 2869442790);

        let mut rng2 = IsaacRng::from_rng(&mut rng1).unwrap();
        assert_eq!(rng2.next_u32(), 3094074039);
    }

    #[test]
    fn test_isaac_true_values_32() {
        let seed = [1,0,0,0, 23,0,0,0, 200,1,0,0, 210,30,0,0,
                     57,48,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
        let mut rng1 = IsaacRng::from_seed(seed);
        let mut results = [0u32; 10];
        for i in results.iter_mut() { *i = rng1.next_u32(); }
        let expected = [
            2558573138, 873787463, 263499565, 2103644246, 3595684709,
            4203127393, 264982119, 2765226902, 2737944514, 3900253796];
        assert_eq!(results, expected);

        let seed = [57,48,0,0, 50,9,1,0, 49,212,0,0, 148,38,0,0,
                    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
        let mut rng2 = IsaacRng::from_seed(seed);
        // skip forward to the 10000th number
        for _ in 0..10000 { rng2.next_u32(); }

        for i in results.iter_mut() { *i = rng2.next_u32(); }
        let expected = [
            3676831399, 3183332890, 2834741178, 3854698763, 2717568474,
            1576568959, 3507990155, 179069555, 141456972, 2478885421];
        assert_eq!(results, expected);
    }

    #[test]
    fn test_isaac_true_values_64() {
        // As above, using little-endian versions of above values
        let seed = [1,0,0,0, 23,0,0,0, 200,1,0,0, 210,30,0,0,
                    57,48,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
        let mut rng = IsaacRng::from_seed(seed);
        let mut results = [0u64; 5];
        for i in results.iter_mut() { *i = rng.next_u64(); }
        let expected = [
            3752888579798383186, 9035083239252078381,18052294697452424037,
            11876559110374379111, 16751462502657800130];
        assert_eq!(results, expected);
    }

    #[test]
    fn test_isaac_true_bytes() {
        let seed = [1,0,0,0, 23,0,0,0, 200,1,0,0, 210,30,0,0,
                     57,48,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
        let mut rng = IsaacRng::from_seed(seed);
        let mut results = [0u8; 32];
        rng.fill_bytes(&mut results);
        // Same as first values in test_isaac_true_values as bytes in LE order
        let expected = [82, 186, 128, 152, 71, 240, 20, 52,
                        45, 175, 180, 15, 86, 16, 99, 125,
                        101, 203, 81, 214, 97, 162, 134, 250,
                        103, 78, 203, 15, 150, 3, 210, 164];
        assert_eq!(results, expected);
    }

    #[test]
    fn test_isaac_new_uninitialized() {
        // Compare the results from initializing `IsaacRng` with
        // `new_from_u64(0)`, to make sure it is the same as the reference
        // implementation when used uninitialized.
        // Note: We only test the first 16 integers, not the full 256 of the
        // first block.
        let mut rng = IsaacRng::new_from_u64(0);
        let mut results = [0u32; 16];
        for i in results.iter_mut() { *i = rng.next_u32(); }
        let expected: [u32; 16] = [
            0x71D71FD2, 0xB54ADAE7, 0xD4788559, 0xC36129FA,
            0x21DC1EA9, 0x3CB879CA, 0xD83B237F, 0xFA3CE5BD,
            0x8D048509, 0xD82E9489, 0xDB452848, 0xCA20E846,
            0x500F972E, 0x0EEFF940, 0x00D6B993, 0xBC12C17F];
        assert_eq!(results, expected);
    }

    #[test]
    fn test_isaac_clone() {
        let seed = [1,0,0,0, 23,0,0,0, 200,1,0,0, 210,30,0,0,
                     57,48,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
        let mut rng1 = IsaacRng::from_seed(seed);
        let mut rng2 = rng1.clone();
        for _ in 0..16 {
            assert_eq!(rng1.next_u32(), rng2.next_u32());
        }
    }

    #[test]
    #[cfg(all(feature="serde-1", feature="std"))]
    fn test_isaac_serde() {
        use bincode;
        use std::io::{BufWriter, BufReader};

        let seed = [1,0,0,0, 23,0,0,0, 200,1,0,0, 210,30,0,0,
                     57,48,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
        let mut rng = IsaacRng::from_seed(seed);

        let buf: Vec<u8> = Vec::new();
        let mut buf = BufWriter::new(buf);
        bincode::serialize_into(&mut buf, &rng, bincode::Infinite).expect("Could not serialize");

        let buf = buf.into_inner().unwrap();
        let mut read = BufReader::new(&buf[..]);
        let mut deserialized: IsaacRng = bincode::deserialize_from(&mut read, bincode::Infinite).expect("Could not deserialize");

        assert_eq!(rng.index, deserialized.index);
        /* Can't assert directly because of the array size */
        for (orig,deser) in rng.rsl.iter().zip(deserialized.rsl.iter()) {
            assert_eq!(orig, deser);
        }
        for (orig,deser) in rng.mem.iter().zip(deserialized.mem.iter()) {
            assert_eq!(orig, deser);
        }
        assert_eq!(rng.a, deserialized.a);
        assert_eq!(rng.b, deserialized.b);
        assert_eq!(rng.c, deserialized.c);

        for _ in 0..16 {
            assert_eq!(rng.next_u64(), deserialized.next_u64());
        }
    }
}
