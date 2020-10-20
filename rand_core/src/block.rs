// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The `BlockRngCore` trait and implementation helpers
//!
//! The [`BlockRngCore`] trait exists to assist in the implementation of RNGs
//! which generate a block of data in a cache instead of returning generated
//! values directly.
//!
//! Usage of this trait is optional, but provides two advantages:
//! implementations only need to concern themselves with generation of the
//! block, not the various [`RngCore`] methods (especially [`fill_bytes`], where
//! the optimal implementations are not trivial), and this allows
//! `ReseedingRng` (see [`rand`](https://docs.rs/rand) crate) perform periodic
//! reseeding with very low overhead.
//!
//! # Example
//!
//! ```no_run
//! use rand_core::{RngCore, SeedableRng};
//! use rand_core::block::{BlockRngCore, BlockRng};
//!
//! struct MyRngCore;
//!
//! #[derive(Eq, PartialEq, Default)]
//! pub struct Results([u64; 8]);
//!
//! impl AsRef<[u64]> for Results {
//!     #[inline(always)]
//!     fn as_ref(&self) -> &[u64] {
//!         &self.0
//!     }
//! }
//!
//! impl BlockRngCore for MyRngCore {
//!     type Results = Results;
//!
//!     fn generate(&mut self, results: &mut Self::Results) {
//!         unimplemented!()
//!     }
//! }
//!
//! impl SeedableRng for MyRngCore {
//!     type Seed = [u8; 32];
//!     fn from_seed(seed: Self::Seed) -> Self {
//!         unimplemented!()
//!     }
//! }
//!
//! // optionally, also implement CryptoRng for MyRngCore
//!
//! // Final RNG.
//! type MyRng = BlockRng<MyRngCore>;
//! let mut rng = MyRng::seed_from_u64(0);
//! println!("First value: {}", rng.next_u32());
//! ```
//!
//! [`BlockRngCore`]: crate::block::BlockRngCore
//! [`fill_bytes`]: RngCore::fill_bytes

use crate::{CryptoRng, Error, RngCore, SeedableRng};
use core::convert::AsRef;
use core::{fmt, slice};
#[cfg(feature = "serde1")]
use serde::{Deserialize, Serialize};

/// A trait for RNGs which do not generate random numbers individually, but in
/// blocks (typically `[u32; N]`). This technique is commonly used by
/// cryptographic RNGs to improve performance.
///
/// See the [module][crate::block] documentation for details.
pub trait BlockRngCore {
    /// Results type. This is the 'block' an RNG implementing `BlockRngCore`
    /// generates, which will usually be an array like `[u8; 64]`.
    type Results: AsRef<[u64]> + Default + Sized;

    /// Generate a new block of results.
    fn generate(&mut self, results: &mut Self::Results);

    /// Try to generate a new block of results.
    #[inline]
    fn try_generate(&mut self, results: &mut Self::Results) -> Result<(), Error> {
        self.generate(results);
        Ok(())
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
enum IndexLevel {
    U1,
    U8,
    U32,
    U64,
}

impl IndexLevel {
    #[inline(always)]
    fn convert(&mut self, index: usize, level: Self) -> usize {
        use IndexLevel::*;
        let res = match (*self, level) {
            (U1, U1) | (U8, U8) | (U32, U32) | (U64, U64) => return index,
            (U1, U8) => (index / 8) + ((index & 0b111) != 0) as usize,
            (U1, U32) => (index / 32) + ((index & 0b1_1111) != 0) as usize,
            (U1, U64) => (index / 64) + ((index & 0b11_1111) != 0) as usize,
            (U8, U1) => 8 * index,
            (U8, U32) => (index / 4) + ((index & 0b11) != 0) as usize,
            (U8, U64) => (index / 8) + ((index & 0b111) != 0) as usize,
            (U32, U1) => 32 * index,
            (U32, U8) => 4 * index,
            (U32, U64) => (index / 2) + ((index & 0b1) != 0) as usize,
            (U64, U1) => 64 * index,
            (U64, U8) => 8 * index,
            (U64, U32) => 2 * index,
        };
        *self = level;
        res
    }
}

/// A wrapper type implementing [`RngCore`] for some type implementing
/// [`BlockRngCore`] with `u32` array buffer; i.e. this can be used to implement
/// a full RNG from just a `generate` function.
///
/// The `core` field may be accessed directly but the results buffer may not.
/// PRNG implementations can simply use a type alias
/// (`pub type MyRng = BlockRng<MyRngCore>;`) but might prefer to use a
/// wrapper type (`pub struct MyRng(BlockRng<MyRngCore>);`); the latter must
/// re-implement `RngCore` but hides the implementation details and allows
/// extra functionality to be defined on the RNG
/// (e.g. `impl MyRng { fn set_stream(...){...} }`).
///
/// `BlockRng` has heavily optimized implementations of the [`RngCore`] methods
/// reading values from the results buffer, as well as
/// calling [`BlockRngCore::generate`] directly on the output array when
/// [`fill_bytes`] / [`try_fill_bytes`] is called on a large array. These methods
/// also handle the bookkeeping of when to generate a new batch of values.
///
/// No whole generated `u32` values are thown away and all values are consumed
/// in-order. [`next_u32`] simply takes the next available `u32` value.
/// [`next_u64`] is implemented by combining two `u32` values, least
/// significant first. [`fill_bytes`] and [`try_fill_bytes`] consume a whole
/// number of `u32` values, converting each `u32` to a byte slice in
/// little-endian order. If the requested byte length is not a multiple of 4,
/// some bytes will be discarded.
///
/// See also [`BlockRng64`] which uses `u64` array buffers. Currently there is
/// no direct support for other buffer types.
///
/// For easy initialization `BlockRng` also implements [`SeedableRng`].
///
/// [`next_u32`]: RngCore::next_u32
/// [`next_u64`]: RngCore::next_u64
/// [`fill_bytes`]: RngCore::fill_bytes
/// [`try_fill_bytes`]: RngCore::try_fill_bytes
#[derive(Clone, Eq, PartialEq)]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
pub struct BlockRng<R: BlockRngCore + Sized> {
    /// The *core* part of the RNG, implementing the `generate` function.
    pub core: R,
    results: R::Results,
    index: usize,
    level: IndexLevel,
}

// Custom Debug implementation that does not expose the contents of `results`.
impl<R: BlockRngCore + fmt::Debug> fmt::Debug for BlockRng<R> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("BlockRng")
            .field("core", &self.core)
            .field("result_len", &self.get_results_u8().len())
            .field("index", &self.index)
            .field("level", &self.level)
            .finish()
    }
}

impl<R: BlockRngCore> BlockRng<R> {
    /// Create a new `BlockRng` from an existing RNG implementing
    /// `BlockRngCore`. Results will be generated on first use.
    #[inline]
    pub fn new(core: R) -> BlockRng<R> {
        let results = R::Results::default();
        let index = 8*results.as_ref().len();
        BlockRng { core, results, index, level: IndexLevel::U8 }
    }

    #[inline(always)]
    fn results_to_u8(results: &R::Results) -> &[u8] {
        let buf = results.as_ref();
        unsafe {
            slice::from_raw_parts(buf.as_ptr() as *const u8, 8 * buf.len())
        }
    }

    #[inline(always)]
    fn get_results_u8(&self) -> &[u8] {
        Self::results_to_u8(&self.results)
    }

    #[inline(always)]
    fn get_results_u32(&self) -> &[u32] {
        let buf = self.results.as_ref();
        unsafe {
            slice::from_raw_parts(buf.as_ptr() as *const u32, 2 * buf.len())
        }
    }

    #[inline(always)]
    fn get_results_u64(&self) -> &[u64] {
        self.results.as_ref()
    }
}

impl<R: BlockRngCore> RngCore for BlockRng<R>
where
    <R as BlockRngCore>::Results: AsRef<[u64]> + Default + Sized,
{
    #[inline]
    fn next_bool(&mut self) -> bool {
        let index = self.level.convert(self.index, IndexLevel::U1);
        match self.get_results_u8().get(index / 8) {
            Some(&v) => {
                self.index = index + 1;
                (v >> (index % 8) & 1) != 0
            }
            None => {
                self.core.generate(&mut self.results);
                self.index = 1;
                (self.get_results_u8()[0] & 1) != 0
            }
        }
    }

    #[inline]
    fn next_u32(&mut self) -> u32 {
        let index = self.level.convert(self.index, IndexLevel::U32);
        match self.get_results_u32().get(index) {
            Some(&v) => {
                self.index = index + 1;
                v
            }
            None => {
                self.core.generate(&mut self.results);
                self.index = 1;
                self.get_results_u32()[0]
            }
        }.to_le()
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        let index = self.level.convert(self.index, IndexLevel::U64);
        match self.get_results_u64().get(index) {
            Some(&v) => {
                self.index = index + 1;
                v
            }
            None => {
                self.core.generate(&mut self.results);
                self.index = 1;
                self.get_results_u64()[0]
            }
        }.to_le()
    }

    #[inline]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.try_fill_bytes(dest).unwrap();
    }

    #[inline]
    fn try_fill_bytes(&mut self, mut dest: &mut [u8]) -> Result<(), Error> {
        let index = self.level.convert(self.index, IndexLevel::U8);

        let rlen = self.get_results_u8().len();
        if index < rlen {
            let dlen = dest.len();
            let res = self.get_results_u8();
            if dlen <= rlen - index {
                dest.copy_from_slice(&res[index..index + dlen]);
                self.index = index + dlen;
                return Ok(());
            } else {
                let (l, r) = dest.split_at_mut(rlen - index);
                l.copy_from_slice(&res[index..]);
                dest = r;
            }
        }

        let mut buf = R::Results::default();
        let mut chunks = dest.chunks_exact_mut(rlen);
        for chunk in &mut chunks {
            self.core.try_generate(&mut buf)?;
            chunk.copy_from_slice(Self::results_to_u8(&buf));
        }

        let rem = chunks.into_remainder();
        if !rem.is_empty() {
            self.core.try_generate(&mut self.results)?;
            rem.copy_from_slice(&self.get_results_u8()[..rem.len()]);
            self.index = rem.len();
        } else {
            self.index = rlen;
        }
        Ok(())
    }
}

impl<R: BlockRngCore + SeedableRng> SeedableRng for BlockRng<R> {
    type Seed = R::Seed;

    #[inline(always)]
    fn from_seed(seed: Self::Seed) -> Self {
        Self::new(R::from_seed(seed))
    }

    #[inline(always)]
    fn seed_from_u64(seed: u64) -> Self {
        Self::new(R::seed_from_u64(seed))
    }

    #[inline(always)]
    fn from_rng<S: RngCore>(rng: S) -> Result<Self, Error> {
        Ok(Self::new(R::from_rng(rng)?))
    }
}

impl<R: BlockRngCore + CryptoRng> CryptoRng for BlockRng<R> {}
