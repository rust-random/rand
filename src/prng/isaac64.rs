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

use {Rng, SeedFromRng, SeedableRng, Result};

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

#[derive(Copy)]
pub struct Isaac64Rng {
    rsl: [w64; RAND_SIZE],
    mem: [w64; RAND_SIZE],
    a: w64,
    b: w64,
    c: w64,
    cnt: u32,
}

static EMPTY_64: Isaac64Rng = Isaac64Rng {
    cnt: 0,
    rsl: [w(0); RAND_SIZE],
    mem: [w(0); RAND_SIZE],
    a: w(0), b: w(0), c: w(0),
};

impl Isaac64Rng {
    /// Create a 64-bit ISAAC random number generator using the
    /// default fixed seed.
    pub fn new_unseeded() -> Isaac64Rng {
        let mut rng = EMPTY_64;
        rng.init(false);
        rng
    }

    /// Initialises `self`. If `use_rsl` is true, then use the current value
    /// of `rsl` as a seed, otherwise construct one algorithmically (not
    /// randomly).
    fn init(&mut self, use_rsl: bool) {
        let mut a = w(0x9e3779b97f4a7c13); // golden ratio
        let mut b = a;
        let mut c = a;
        let mut d = a;
        let mut e = a;
        let mut f = a;
        let mut g = a;
        let mut h = a;

        macro_rules! mix {
            () => {{
                a -= e; f ^= h >> 9;  h += a;
                b -= f; g ^= a << 9;  a += b;
                c -= g; h ^= b >> 23; b += c;
                d -= h; a ^= c << 15; c += d;
                e -= a; b ^= d >> 14; d += e;
                f -= b; c ^= e << 20; e += f;
                g -= c; d ^= f >> 17; f += g;
                h -= d; e ^= g << 14; g += h;
            }}
        }

        for _ in 0..4 {
            mix!();
        }

        if use_rsl {
            macro_rules! memloop {
                ($arr:expr) => {{
                    for i in (0..RAND_SIZE/8).map(|i| i * 8) {
                        a += $arr[i  ]; b += $arr[i+1];
                        c += $arr[i+2]; d += $arr[i+3];
                        e += $arr[i+4]; f += $arr[i+5];
                        g += $arr[i+6]; h += $arr[i+7];
                        mix!();
                        self.mem[i  ] = a; self.mem[i+1] = b;
                        self.mem[i+2] = c; self.mem[i+3] = d;
                        self.mem[i+4] = e; self.mem[i+5] = f;
                        self.mem[i+6] = g; self.mem[i+7] = h;
                    }
                }}
            }

            memloop!(self.rsl);
            memloop!(self.mem);
        } else {
            for i in (0..RAND_SIZE/8).map(|i| i * 8) {
                mix!();
                self.mem[i  ] = a; self.mem[i+1] = b;
                self.mem[i+2] = c; self.mem[i+3] = d;
                self.mem[i+4] = e; self.mem[i+5] = f;
                self.mem[i+6] = g; self.mem[i+7] = h;
            }
        }

        self.isaac64();
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
    fn isaac64(&mut self) {
        self.c += w(1);
        // abbreviations
        let mut a = self.a;
        let mut b = self.b + self.c;
        const MIDPOINT: usize = RAND_SIZE / 2;

        #[inline(always)]
        fn ind(mem:&[w64; RAND_SIZE], v: w64, amount: usize) -> w64 {
            let index = (v >> amount).0 as usize % RAND_SIZE;
            mem[index]
        }

        #[inline(always)]
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
            ctx.rsl[base + m] = *b;
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
        self.cnt = RAND_SIZE as u32;
    }
}

// Cannot be derived because [u32; 256] does not implement Clone
impl Clone for Isaac64Rng {
    fn clone(&self) -> Isaac64Rng {
        *self
    }
}

impl Rng for Isaac64Rng {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        self.next_u64() as u32
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        if self.cnt == 0 {
            // make some more numbers
            self.isaac64();
        }
        self.cnt -= 1;

        // self.cnt is at most RAND_SIZE, but that is before the
        // subtraction above. We want to index without bounds
        // checking, but this could lead to incorrect code if someone
        // misrefactors, so we check, sometimes.
        //
        // (Changes here should be reflected in IsaacRng.next_u32.)
        debug_assert!((self.cnt as usize) < RAND_SIZE);

        // (the % is cheaply telling the optimiser that we're always
        // in bounds, without unsafe. NB. this is a power of two, so
        // it optimises to a bitwise mask).
        self.rsl[self.cnt as usize % RAND_SIZE].0
    }
    
    #[cfg(feature = "i128_support")]
    fn next_u128(&mut self) -> u128 {
        ::rand_core::impls::next_u128_via_u64(self)
    }
    
    fn try_fill(&mut self, dest: &mut [u8]) -> Result<()> {
        ::rand_core::impls::try_fill_via_u32(self, dest)
    }
}

impl SeedFromRng for Isaac64Rng {
    fn from_rng<R: Rng+?Sized>(other: &mut R) -> Result<Self> {
        let mut ret = EMPTY_64;
        unsafe {
            let ptr = ret.rsl.as_mut_ptr() as *mut u8;

            let slice = slice::from_raw_parts_mut(ptr, RAND_SIZE * 8);
            other.try_fill(slice)?;
        }
        ret.cnt = 0;
        ret.a = w(0);
        ret.b = w(0);
        ret.c = w(0);

        ret.init(true);
        Ok(ret)
    }
}

impl<'a> SeedableRng<&'a [u64]> for Isaac64Rng {
    /// Create an ISAAC random number generator with a seed. This can
    /// be any length, although the maximum number of elements used is
    /// 256 and any more will be silently ignored. A generator
    /// constructed with a given seed will generate the same sequence
    /// of values as all other generators constructed with that seed.
    fn from_seed(seed: &'a [u64]) -> Isaac64Rng {
        let mut rng = EMPTY_64;

        // make the seed into [seed[0], seed[1], ..., seed[seed.len()
        // - 1], 0, 0, ...], to fill rng.rsl.
        let seed_iter = seed.iter().map(|&x| x).chain(repeat(0u64));

        for (rsl_elem, seed_elem) in rng.rsl.iter_mut().zip(seed_iter) {
            *rsl_elem = w(seed_elem);
        }
        rng.init(true);
        rng
    }
}

impl fmt::Debug for Isaac64Rng {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Isaac64Rng {{}}")
    }
}

#[cfg(test)]
mod test {
    use {Rng, SeedableRng, iter};
    use distributions::ascii_word_char;
    use super::Isaac64Rng;

    #[test]
    fn test_rng_64_rand_seeded() {
        let s = iter(&mut ::test::rng()).map(|rng| rng.next_u64()).take(256).collect::<Vec<u64>>();
        let mut ra: Isaac64Rng = SeedableRng::from_seed(&s[..]);
        let mut rb: Isaac64Rng = SeedableRng::from_seed(&s[..]);
        assert!(::test::iter_eq(iter(&mut ra).map(|rng| ascii_word_char(rng)).take(100),
                                iter(&mut rb).map(|rng| ascii_word_char(rng)).take(100)));
    }

    #[test]
    fn test_rng_64_seeded() {
        let seed: &[_] = &[1, 23, 456, 7890, 12345];
        let mut ra: Isaac64Rng = SeedableRng::from_seed(seed);
        let mut rb: Isaac64Rng = SeedableRng::from_seed(seed);
        assert!(::test::iter_eq(iter(&mut ra).map(|rng| ascii_word_char(rng)).take(100),
                                iter(&mut rb).map(|rng| ascii_word_char(rng)).take(100)));
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
    fn test_rng_clone() {
        let seed: &[_] = &[1, 23, 456, 7890, 12345];
        let mut rng: Isaac64Rng = SeedableRng::from_seed(seed);
        let mut clone = rng.clone();
        for _ in 0..16 {
            assert_eq!(rng.next_u64(), clone.next_u64());
        }
    }
}
