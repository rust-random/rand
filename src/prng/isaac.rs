// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The ISAAC random number generator.

use core::slice;
use core::iter::repeat;
use core::num::Wrapping as w;
use core::fmt;

use {Rng, SeedFromRng, SeedableRng, Result};

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
/// [1]: Bob Jenkins, [*ISAAC: A fast cryptographic random number generator*]
///      (http://burtleburtle.net/bob/rand/isaacafa.html)
///
/// [2]: Bob Jenkins, [*ISAAC and RC4*]
///      (http://burtleburtle.net/bob/rand/isaac.html)
///
/// [3]: Jean-Philippe Aumasson, [*On the pseudo-random generator ISAAC*]
///      (http://eprint.iacr.org/2006/438)

#[derive(Copy)]
pub struct IsaacRng {
    rsl: [w32; RAND_SIZE],
    mem: [w32; RAND_SIZE],
    a: w32,
    b: w32,
    c: w32,
    cnt: u32,
}

static EMPTY: IsaacRng = IsaacRng {
    cnt: 0,
    rsl: [w(0); RAND_SIZE],
    mem: [w(0); RAND_SIZE],
    a: w(0), b: w(0), c: w(0),
};

impl IsaacRng {
    /// Create an ISAAC random number generator using the default
    /// fixed seed.
    pub fn new_unseeded() -> IsaacRng {
        let mut rng = EMPTY;
        rng.init(false);
        rng
    }

    /// Initialises `self`. If `use_rsl` is true, then use the current value
    /// of `rsl` as a seed, otherwise construct one algorithmically (not
    /// randomly).
    fn init(&mut self, use_rsl: bool) {
        let mut a = w(0x9e3779b9); // golden ratio
        let mut b = a;
        let mut c = a;
        let mut d = a;
        let mut e = a;
        let mut f = a;
        let mut g = a;
        let mut h = a;

        macro_rules! mix {
            () => {{
                a ^= b << 11; d += a; b += c;
                b ^= c >> 2;  e += b; c += d;
                c ^= d << 8;  f += c; d += e;
                d ^= e >> 16; g += d; e += f;
                e ^= f << 10; h += e; f += g;
                f ^= g >> 4;  a += f; g += h;
                g ^= h << 8;  b += g; h += a;
                h ^= a >> 9;  c += h; a += b;
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

        self.isaac();
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
    fn isaac(&mut self) {
        self.c += w(1);
        // abbreviations
        let mut a = self.a;
        let mut b = self.b + self.c;
        const MIDPOINT: usize = RAND_SIZE / 2;

        #[inline(always)]
        fn ind(mem:&[w32; RAND_SIZE], v: w32, amount: usize) -> w32 {
            let index = (v >> amount).0 as usize % RAND_SIZE;
            mem[index]
        }

        #[inline(always)]
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
            ctx.rsl[base + m] = *b;
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
        self.cnt = RAND_SIZE as u32;
    }
}

// Cannot be derived because [u32; 256] does not implement Clone
impl Clone for IsaacRng {
    fn clone(&self) -> IsaacRng {
        *self
    }
}

impl Rng for IsaacRng {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        if self.cnt == 0 {
            // make some more numbers
            self.isaac();
        }
        self.cnt -= 1;

        // self.cnt is at most RAND_SIZE, but that is before the
        // subtraction above. We want to index without bounds
        // checking, but this could lead to incorrect code if someone
        // misrefactors, so we check, sometimes.
        //
        // (Changes here should be reflected in Isaac64Rng.next_u64.)
        debug_assert!((self.cnt as usize) < RAND_SIZE);

        // (the % is cheaply telling the optimiser that we're always
        // in bounds, without unsafe. NB. this is a power of two, so
        // it optimises to a bitwise mask).
        self.rsl[self.cnt as usize % RAND_SIZE].0
    }
    
    fn next_u64(&mut self) -> u64 {
        ::rand_core::impls::next_u64_via_u32(self)
    }
    #[cfg(feature = "i128_support")]
    fn next_u128(&mut self) -> u128 {
        ::rand_core::impls::next_u128_via_u64(self)
    }
    
    fn try_fill(&mut self, dest: &mut [u8]) -> Result<()> {
        ::rand_core::impls::try_fill_via_u32(self, dest)
    }
}

impl SeedFromRng for IsaacRng {
    fn from_rng<R: Rng+?Sized>(other: &mut R) -> Result<Self> {
        let mut ret = EMPTY;
        unsafe {
            let ptr = ret.rsl.as_mut_ptr() as *mut u8;

            let slice = slice::from_raw_parts_mut(ptr, RAND_SIZE * 4);
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

impl<'a> SeedableRng<&'a [u32]> for IsaacRng {
    /// Create an ISAAC random number generator with a seed. This can
    /// be any length, although the maximum number of elements used is
    /// 256 and any more will be silently ignored. A generator
    /// constructed with a given seed will generate the same sequence
    /// of values as all other generators constructed with that seed.
    fn from_seed(seed: &'a [u32]) -> IsaacRng {
        let mut rng = EMPTY;

        // make the seed into [seed[0], seed[1], ..., seed[seed.len()
        // - 1], 0, 0, ...], to fill rng.rsl.
        let seed_iter = seed.iter().map(|&x| x).chain(repeat(0u32));

        for (rsl_elem, seed_elem) in rng.rsl.iter_mut().zip(seed_iter) {
            *rsl_elem = w(seed_elem);
        }
        rng.init(true);
        rng
    }
}

impl fmt::Debug for IsaacRng {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "IsaacRng {{}}")
    }
}

#[cfg(test)]
mod test {
    use {Rng, SeedableRng, iter};
    use distributions::ascii_word_char;
    use super::IsaacRng;

    #[test]
    fn test_rng_32_rand_seeded() {
        let s = iter(&mut ::test::rng()).map(|rng| rng.next_u32()).take(256).collect::<Vec<u32>>();
        let mut ra: IsaacRng = SeedableRng::from_seed(&s[..]);
        let mut rb: IsaacRng = SeedableRng::from_seed(&s[..]);
        assert!(::test::iter_eq(iter(&mut ra).map(|rng| ascii_word_char(rng)).take(100),
                                iter(&mut rb).map(|rng| ascii_word_char(rng)).take(100)));
    }

    #[test]
    fn test_rng_32_seeded() {
        let seed: &[_] = &[1, 23, 456, 7890, 12345];
        let mut ra: IsaacRng = SeedableRng::from_seed(seed);
        let mut rb: IsaacRng = SeedableRng::from_seed(seed);
        assert!(::test::iter_eq(iter(&mut ra).map(|rng| ascii_word_char(rng)).take(100),
                                iter(&mut rb).map(|rng| ascii_word_char(rng)).take(100)));
    }

    #[test]
    fn test_rng_32_true_values() {
        let seed: &[_] = &[1, 23, 456, 7890, 12345];
        let mut ra: IsaacRng = SeedableRng::from_seed(seed);
        // Regression test that isaac is actually using the above vector
        let v = (0..10).map(|_| ra.next_u32()).collect::<Vec<_>>();
        assert_eq!(v,
                   vec!(2558573138, 873787463, 263499565, 2103644246, 3595684709,
                        4203127393, 264982119, 2765226902, 2737944514, 3900253796));

        let seed: &[_] = &[12345, 67890, 54321, 9876];
        let mut rb: IsaacRng = SeedableRng::from_seed(seed);
        // skip forward to the 10000th number
        for _ in 0..10000 { rb.next_u32(); }

        let v = (0..10).map(|_| rb.next_u32()).collect::<Vec<_>>();
        assert_eq!(v,
                   vec!(3676831399, 3183332890, 2834741178, 3854698763, 2717568474,
                        1576568959, 3507990155, 179069555, 141456972, 2478885421));
    }

    #[test]
    fn test_rng_clone() {
        let seed: &[_] = &[1, 23, 456, 7890, 12345];
        let mut rng: IsaacRng = SeedableRng::from_seed(seed);
        let mut clone = rng.clone();
        for _ in 0..16 {
            assert_eq!(rng.next_u32(), clone.next_u32());
        }
    }
}
