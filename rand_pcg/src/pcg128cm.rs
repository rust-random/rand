// Copyright 2018-2021 Developers of the Rand project.
// Copyright 2017 Paul Dicker.
// Copyright 2014-2017, 2019 Melissa O'Neill and PCG Project contributors
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! PCG random number generators

// This is the cheap multiplier used by PCG for 128-bit state.
const MULTIPLIER: u64 = 15750249268501108917;

use core::fmt;
use rand_core::{RngCore, SeedableRng, le};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A PCG random number generator (CM DXSM 128/64 (LCG) variant).
///
/// Permuted Congruential Generator with 128-bit state, internal Linear
/// Congruential Generator, and 64-bit output via "double xorshift multiply"
/// output function.
///
/// This is a 128-bit LCG with explicitly chosen stream with the PCG-DXSM
/// output function. This corresponds to `pcg_engines::cm_setseq_dxsm_128_64`
/// from pcg_cpp and `PCG64DXSM` from NumPy.
///
/// Despite the name, this implementation uses 32 bytes (256 bit) space
/// comprising 128 bits of state and 128 bits stream selector. These are both
/// set by `SeedableRng`, using a 256-bit seed.
///
/// Note that while two generators with different stream parameter may be
/// closely correlated, this is [mitigated][upgrading-pcg64] by the DXSM output function.
///
/// [upgrading-pcg64]: https://numpy.org/doc/stable/reference/random/upgrading-pcg64.html
#[derive(Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Lcg128CmDxsm64 {
    state: u128,
    increment: u128,
}

/// [`Lcg128CmDxsm64`] is also known as `PCG64DXSM`.
pub type Pcg64Dxsm = Lcg128CmDxsm64;

impl Lcg128CmDxsm64 {
    /// Multi-step advance functions (jump-ahead, jump-back)
    ///
    /// The method used here is based on Brown, "Random Number Generation
    /// with Arbitrary Stride,", Transactions of the American Nuclear
    /// Society (Nov. 1994).  The algorithm is very similar to fast
    /// exponentiation.
    ///
    /// Even though delta is an unsigned integer, we can pass a
    /// signed integer to go backwards, it just goes "the long way round".
    ///
    /// Using this function is equivalent to calling `next_64()` `delta`
    /// number of times.
    #[inline]
    pub fn advance(&mut self, delta: u128) {
        let mut acc_mult: u128 = 1;
        let mut acc_plus: u128 = 0;
        let mut cur_mult = MULTIPLIER as u128;
        let mut cur_plus = self.increment;
        let mut mdelta = delta;

        while mdelta > 0 {
            if (mdelta & 1) != 0 {
                acc_mult = acc_mult.wrapping_mul(cur_mult);
                acc_plus = acc_plus.wrapping_mul(cur_mult).wrapping_add(cur_plus);
            }
            cur_plus = cur_mult.wrapping_add(1).wrapping_mul(cur_plus);
            cur_mult = cur_mult.wrapping_mul(cur_mult);
            mdelta /= 2;
        }
        self.state = acc_mult.wrapping_mul(self.state).wrapping_add(acc_plus);
    }

    /// Construct an instance compatible with PCG seed and stream.
    ///
    /// Note that the highest bit of the `stream` parameter is discarded
    /// to simplify upholding internal invariants.
    ///
    /// Note that while two generators with different stream parameter may be
    /// closely correlated, this is [mitigated][upgrading-pcg64] by the DXSM output function.
    ///
    /// PCG specifies the following default values for both parameters:
    ///
    /// - `state = 0xcafef00dd15ea5e5`
    /// - `stream = 0xa02bdbf7bb3c0a7ac28fa16a64abf96`
    ///
    /// [upgrading-pcg64]: https://numpy.org/doc/stable/reference/random/upgrading-pcg64.html
    pub fn new(state: u128, stream: u128) -> Self {
        // The increment must be odd, hence we discard one bit:
        let increment = (stream << 1) | 1;
        Self::from_state_incr(state, increment)
    }

    #[inline]
    fn from_state_incr(state: u128, increment: u128) -> Self {
        let mut pcg = Self { state, increment };
        // Move away from initial value:
        pcg.state = pcg.state.wrapping_add(pcg.increment);
        pcg.step();
        pcg
    }

    #[inline(always)]
    fn step(&mut self) {
        // prepare the LCG for the next round
        self.state = self
            .state
            .wrapping_mul(MULTIPLIER as u128)
            .wrapping_add(self.increment);
    }
}

// Custom Debug implementation that does not expose the internal state
impl fmt::Debug for Lcg128CmDxsm64 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Lcg128CmDxsm64 {{}}")
    }
}

impl SeedableRng for Lcg128CmDxsm64 {
    type Seed = [u8; 32];

    /// We use a single 255-bit seed to initialise the state and select a stream.
    /// One `seed` bit (lowest bit of `seed[8]`) is ignored.
    fn from_seed(seed: Self::Seed) -> Self {
        let mut seed_u64 = [0u64; 4];
        le::read_u64_into(&seed, &mut seed_u64);
        let state = u128::from(seed_u64[0]) | (u128::from(seed_u64[1]) << 64);
        let incr = u128::from(seed_u64[2]) | (u128::from(seed_u64[3]) << 64);

        // The increment must be odd, hence we discard one bit:
        Self::from_state_incr(state, incr | 1)
    }
}

impl RngCore for Lcg128CmDxsm64 {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        self.next_u64() as u32
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        let res = output_dxsm(self.state);
        self.step();
        res
    }

    #[inline]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        le::fill_bytes_via_next(self, dest)
    }
}

#[inline(always)]
fn output_dxsm(state: u128) -> u64 {
    // See https://github.com/imneme/pcg-cpp/blob/ffd522e7188bef30a00c74dc7eb9de5faff90092/include/pcg_random.hpp#L1016
    // for a short discussion of the construction and its original implementation.
    let mut hi = (state >> 64) as u64;
    let mut lo = state as u64;

    lo |= 1;
    hi ^= hi >> 32;
    hi = hi.wrapping_mul(MULTIPLIER);
    hi ^= hi >> 48;
    hi = hi.wrapping_mul(lo);

    hi
}
