// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The ISAAC-64 random number generator.

use core::slice;
use core::iter::repeat;
use core::num::Wrapping as w;
use core::fmt;

use {Rng, SeedableRng, Rand};
use impls;

#[allow(non_camel_case_types)]
type w64 = w<u64>;

const RAND_SIZE_LEN: usize = 8;
const RAND_SIZE: usize = 1 << RAND_SIZE_LEN;

/// A random number generator that uses ISAAC-64, the 64-bit variant of the
/// ISAAC algorithm.
///
/// ISAAC stands for "Indirection, Shift, Accumulate, Add, and Count" which are
/// the principal bitwise operations employed. It is the most advanced of a
/// series of array based random number generator designed by Robert Jenkins
/// in 1996[1].
///
/// Although ISAAC is designed to be cryptographically secure, its design is not
/// founded in cryptographic theory. Therefore it is _not recommended for_
/// cryptographic purposes. It is however one of the strongest non-cryptograpic
/// RNGs, and that while still being reasonably fast.
///
/// ISAAC-64 is mostly similar to ISAAC. Because it operates on 64-bit integers
/// instead of 32-bit, it uses twice as much memory to hold its state and
/// results. Also it uses different constants for shifts and indirect indexing,
/// optimized to give good results for 64bit arithmetic.
///
/// ## Overview of the ISAAC-64 algorithm:
/// (in pseudo-code)
///
/// ```text
/// Input: a, b, c, s[256] // state
/// Output: r[256] // results
///
/// mix(a,i) = !(a ^ a << 21)  if i = 0 mod 4
///              a ^ a >>  5   if i = 1 mod 4
///              a ^ a << 12   if i = 2 mod 4
///              a ^ a >> 33   if i = 3 mod 4
///
/// c = c + 1
/// b = b + c
///
/// for i in 0..256 {
///     x = s_[i]
///     a = mix(a,i) + s[i+128 mod 256]
///     y = a + b + s[x>>3 mod 256]
///     s[i] = y
///     b = x + s[y>>11 mod 256]
///     r[i] = b
/// }
/// ```
///
/// See for more information the description in rand::prng::IsaacRng.
///
/// [1]: Bob Jenkins, [*ISAAC and RC4*]
///      (http://burtleburtle.net/bob/rand/isaac.html)
pub struct Isaac64Rng {
    rsl: [u64; RAND_SIZE],
    mem: [w64; RAND_SIZE],
    a: w64,
    b: w64,
    c: w64,
    index: u32,
    half_used: bool, // true if only half of the previous result is used
}

// Cannot be derived because [u64; 256] does not implement Clone
// FIXME: remove once RFC 2000 gets implemented
impl Clone for Isaac64Rng {
    fn clone(&self) -> Isaac64Rng {
        Isaac64Rng {
            rsl: self.rsl,
            mem: self.mem,
            a: self.a,
            b: self.b,
            c: self.c,
            index: self.index,
            half_used: self.half_used,
        }
    }
}

// Custom Debug implementation that does not expose the internal state
impl fmt::Debug for Isaac64Rng {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Isaac64Rng {{}}")
    }
}

impl Isaac64Rng {
    /// Create a 64-bit ISAAC random number generator using the
    /// default fixed seed.
    pub fn new_unseeded() -> Isaac64Rng {
        Self::new_from_u64(0)
    }
    
    /// Creates an ISAAC-64 random number generator using an u64 as seed.
    /// If `seed == 0` this will produce the same stream of random numbers as
    /// the reference implementation when used unseeded.
    pub fn new_from_u64(seed: u64) -> Isaac64Rng {
        let mut key = [w(0); RAND_SIZE];
        key[0] = w(seed);
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
    fn isaac64(&mut self) {
        self.c += w(1);
        // abbreviations
        let mut a = self.a;
        let mut b = self.b + self.c;
        const MIDPOINT: usize = RAND_SIZE / 2;

        #[inline]
        fn ind(mem:&[w64; RAND_SIZE], v: w64, amount: usize) -> w64 {
            let index = (v >> amount).0 as usize % RAND_SIZE;
            mem[index]
        }

        #[inline]
        fn rngstep(ctx: &mut Isaac64Rng,
                   mix: w64,
                   a: &mut w64,
                   b: &mut w64,
                   base: usize,
                   m: usize,
                   m2: usize) {
            let x = ctx.mem[base + m];
            *a = mix + ctx.mem[base + m2];
            let y = *a + *b + ind(&ctx.mem, x, 3);
            ctx.mem[base + m] = y;
            *b = x + ind(&ctx.mem, y, 3 + RAND_SIZE_LEN);
            ctx.rsl[RAND_SIZE - 1 - base - m] = (*b).0;
        }

        let mut m = 0;
        let mut m2 = MIDPOINT;
        for i in (0..MIDPOINT/4).map(|i| i * 4) {
            rngstep(self, !(a ^ (a << 21)), &mut a, &mut b, i + 0, m, m2);
            rngstep(self,   a ^ (a >> 5 ),  &mut a, &mut b, i + 1, m, m2);
            rngstep(self,   a ^ (a << 12),  &mut a, &mut b, i + 2, m, m2);
            rngstep(self,   a ^ (a >> 33),  &mut a, &mut b, i + 3, m, m2);
        }

        m = MIDPOINT;
        m2 = 0;
        for i in (0..MIDPOINT/4).map(|i| i * 4) {
            rngstep(self, !(a ^ (a << 21)), &mut a, &mut b, i + 0, m, m2);
            rngstep(self,   a ^ (a >> 5 ),  &mut a, &mut b, i + 1, m, m2);
            rngstep(self,   a ^ (a << 12),  &mut a, &mut b, i + 2, m, m2);
            rngstep(self,   a ^ (a >> 33),  &mut a, &mut b, i + 3, m, m2);
        }

        self.a = a;
        self.b = b;
        self.index = 0;
        self.half_used = false;
    }
}

impl Rng for Isaac64Rng {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        // Using a local variable for `index`, and checking the size avoids a
        // bounds check later on.
        let mut index = self.index as usize * 2 - self.half_used as usize;
        if index >= RAND_SIZE * 2 {
            self.isaac64();
            index = 0;
        }

        self.half_used = !self.half_used;
        self.index += self.half_used as u32;

        // Index as if this is a u32 slice.
        let rsl = unsafe { &*(&mut self.rsl as *mut [u64; RAND_SIZE]
                                            as *mut [u32; RAND_SIZE * 2]) };

        if cfg!(target_endian = "little") {
            rsl[index]
        } else {
            rsl[index ^ 1]
        }
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        let mut index = self.index as usize;
        if index >= RAND_SIZE {
            self.isaac64();
            index = 0;
        }

        let value = self.rsl[index];
        self.index += 1;
        self.half_used = false;
        value
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        let mut read_len = 0;
        while read_len < dest.len() {
            if self.index as usize >= RAND_SIZE {
                self.isaac64();
            }

            let (consumed_u64, filled_u8) =
                impls::fill_via_u64_chunks(&mut self.rsl[self.index as usize..],
                                           &mut dest[read_len..]);

            self.index += consumed_u64 as u32;
            read_len += filled_u8;
        }
    }
}

/// Creates a new ISAAC-64 random number generator.
fn init(mut mem: [w64; RAND_SIZE], rounds: u32) -> Isaac64Rng {
    // These numbers are the result of initializing a...h with the
    // fractional part of the golden ratio in binary (0x9e3779b97f4a7c13)
    // and applying mix() 4 times.
    let mut a = w(0x647c4677a2884b7c);
    let mut b = w(0xb9f8b322c73ac862);
    let mut c = w(0x8c0ea5053d4712a0);
    let mut d = w(0xb29b2e824a595524);
    let mut e = w(0x82f053db8355e0ce);
    let mut f = w(0x48fe4a0fa5a09315);
    let mut g = w(0xae985bf2cbfc89ed);
    let mut h = w(0x98f5704f6c44c0ab);

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

    let mut rng = Isaac64Rng {
        rsl: [0; RAND_SIZE],
        mem: mem,
        a: w(0),
        b: w(0),
        c: w(0),
        index: 0,
        half_used: false,
    };

    // Prepare the first set of results
    rng.isaac64();
    rng
}

fn mix(a: &mut w64, b: &mut w64, c: &mut w64, d: &mut w64,
       e: &mut w64, f: &mut w64, g: &mut w64, h: &mut w64) {
    *a -= *e; *f ^= *h >> 9;  *h += *a;
    *b -= *f; *g ^= *a << 9;  *a += *b;
    *c -= *g; *h ^= *b >> 23; *b += *c;
    *d -= *h; *a ^= *c << 15; *c += *d;
    *e -= *a; *b ^= *d >> 14; *d += *e;
    *f -= *b; *c ^= *e << 20; *e += *f;
    *g -= *c; *d ^= *f >> 17; *f += *g;
    *h -= *d; *e ^= *g << 14; *g += *h;
}

impl Rand for Isaac64Rng {
    fn rand<R: Rng>(other: &mut R) -> Isaac64Rng {
        let mut key = [w(0); RAND_SIZE];
        unsafe {
            let ptr = key.as_mut_ptr() as *mut u8;

            let slice = slice::from_raw_parts_mut(ptr, RAND_SIZE * 8);
            other.fill_bytes(slice);
        }
        init(key, 2)
    }
}

impl<'a> SeedableRng<&'a [u64]> for Isaac64Rng {
    fn reseed(&mut self, seed: &'a [u64]) {
        *self = Self::from_seed(seed);
    }

    /// Create an ISAAC random number generator with a seed. This can
    /// be any length, although the maximum number of elements used is
    /// 256 and any more will be silently ignored. A generator
    /// constructed with a given seed will generate the same sequence
    /// of values as all other generators constructed with that seed.
    fn from_seed(seed: &'a [u64]) -> Isaac64Rng {
        let mut key = [w(0); RAND_SIZE];

        // make the seed into [seed[0], seed[1], ..., seed[seed.len()
        // - 1], 0, 0, ...], to fill `key`.
        let seed_iter = seed.iter().map(|&x| x).chain(repeat(0u64));

        for (rsl_elem, seed_elem) in key.iter_mut().zip(seed_iter) {
            *rsl_elem = w(seed_elem);
        }

        init(key, 2)
    }
}

#[cfg(test)]
mod test {
    use {Rng, SeedableRng};
    use super::Isaac64Rng;

    #[test]
    fn test_rng_64_rand_seeded() {
        let s = ::test::rng().gen_iter::<u64>().take(256).collect::<Vec<u64>>();
        let mut ra: Isaac64Rng = SeedableRng::from_seed(&s[..]);
        let mut rb: Isaac64Rng = SeedableRng::from_seed(&s[..]);
        assert!(::test::iter_eq(ra.gen_ascii_chars().take(100),
                                rb.gen_ascii_chars().take(100)));
    }

    #[test]
    fn test_rng_64_seeded() {
        let seed: &[_] = &[1, 23, 456, 7890, 12345];
        let mut ra: Isaac64Rng = SeedableRng::from_seed(seed);
        let mut rb: Isaac64Rng = SeedableRng::from_seed(seed);
        assert!(::test::iter_eq(ra.gen_ascii_chars().take(100),
                                rb.gen_ascii_chars().take(100)));
    }

    #[test]
    fn test_rng_64_reseed() {
        let s = ::test::rng().gen_iter::<u64>().take(256).collect::<Vec<u64>>();
        let mut r: Isaac64Rng = SeedableRng::from_seed(&s[..]);
        let string1: String = r.gen_ascii_chars().take(100).collect();

        r.reseed(&s[..]);

        let string2: String = r.gen_ascii_chars().take(100).collect();
        assert_eq!(string1, string2);
    }

    #[test]
    fn test_rng_64_true_values() {
        let seed: &[_] = &[1, 23, 456, 7890, 12345];
        let mut ra: Isaac64Rng = SeedableRng::from_seed(seed);
        // Regression test that isaac is actually using the above vector
        let v = (0..10).map(|_| ra.next_u64()).collect::<Vec<_>>();
        assert_eq!(v,
                   vec!(547121783600835980, 14377643087320773276, 17351601304698403469,
                        1238879483818134882, 11952566807690396487, 13970131091560099343,
                        4469761996653280935, 15552757044682284409, 6860251611068737823,
                        13722198873481261842));

        let seed: &[_] = &[12345, 67890, 54321, 9876];
        let mut rb: Isaac64Rng = SeedableRng::from_seed(seed);
        // skip forward to the 10000th number
        for _ in 0..10000 { rb.next_u64(); }

        let v = (0..10).map(|_| rb.next_u64()).collect::<Vec<_>>();
        assert_eq!(v,
                   vec!(18143823860592706164, 8491801882678285927, 2699425367717515619,
                        17196852593171130876, 2606123525235546165, 15790932315217671084,
                        596345674630742204, 9947027391921273664, 11788097613744130851,
                        10391409374914919106));
    }

    #[test]
    fn test_isaac64_true_values_32() {
        let seed: &[_] = &[1, 23, 456, 7890, 12345];
        let mut rng1 = Isaac64Rng::from_seed(seed);
        let v = (0..12).map(|_| rng1.next_u32()).collect::<Vec<_>>();
        // Subset of above values, as an LE u32 sequence
        assert_eq!(v,
                   [141028748, 127386717,
                    1058730652, 3347555894,
                    851491469, 4039984500,
                    2692730210, 288449107,
                    646103879, 2782923823,
                    4195642895, 3252674613]);
    }

    #[test]
    fn test_isaac64_true_values_mixed() {
        let seed: &[_] = &[1, 23, 456, 7890, 12345];
        let mut rng = Isaac64Rng::from_seed(seed);
        // Test alternating between `next_u64` and `next_u32` works as expected.
        // Values are the same as `test_isaac64_true_values` and
        // `test_isaac64_true_values_32`.
        assert_eq!(rng.next_u64(), 547121783600835980);
        assert_eq!(rng.next_u32(), 1058730652);
        assert_eq!(rng.next_u32(), 3347555894);
        assert_eq!(rng.next_u64(), 17351601304698403469);
        assert_eq!(rng.next_u32(), 2692730210);
        // Skip one u32
        assert_eq!(rng.next_u64(), 11952566807690396487);
        assert_eq!(rng.next_u32(), 4195642895);
    }

    #[test]
    fn test_isaac64_true_bytes() {
        let seed: &[_] = &[1, 23, 456, 7890, 12345];
        let mut rng1 = Isaac64Rng::from_seed(seed);
        let mut buf = [0u8; 32];
        rng1.fill_bytes(&mut buf);
        // Same as first values in test_isaac64_true_values as bytes in LE order
        assert_eq!(buf,
                   [140, 237, 103, 8, 93, 196, 151, 7,
                    156, 242, 26, 63, 54, 166, 135, 199,
                    141, 186, 192, 50, 116, 69, 205, 240,
                    98, 205, 127, 160, 83, 98, 49, 17]);
    }

    #[test]
    fn test_isaac_new_uninitialized() {
        // Compare the results from initializing `IsaacRng` with
        // `new_from_u64(0)`, to make sure it is the same as the reference
        // implementation when used uninitialized.
        // Note: We only test the first 16 integers, not the full 256 of the
        // first block.
        let mut rng = Isaac64Rng::new_from_u64(0);
        let vec = (0..16).map(|_| rng.next_u64()).collect::<Vec<_>>();
        let expected: [u64; 16] = [
            0xF67DFBA498E4937C, 0x84A5066A9204F380, 0xFEE34BD5F5514DBB,
            0x4D1664739B8F80D6, 0x8607459AB52A14AA, 0x0E78BC5A98529E49,
            0xFE5332822AD13777, 0x556C27525E33D01A, 0x08643CA615F3149F,
            0xD0771FAF3CB04714, 0x30E86F68A37B008D, 0x3074EBC0488A3ADF,
            0x270645EA7A2790BC, 0x5601A0A8D3763C6A, 0x2F83071F53F325DD,
            0xB9090F3D42D2D2EA];
        assert_eq!(vec, expected);
    }

    #[test]
    fn test_rng_clone() {
        let seed: &[_] = &[1, 23, 456, 7890, 12345];
        let mut rng: Isaac64Rng = SeedableRng::from_seed(seed);
        let mut clone = rng.clone();
        for _ in 0..16 {
            assert_eq!(rng.next_u64(), clone.next_u64());
        }
    }
}
