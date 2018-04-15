// Copyright 2013-2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Helper functions for implementing `RngCore` functions.
//!
//! For cross-platform reproducibility, these functions all use Little Endian:
//! least-significant part first. For example, `next_u64_via_u32` takes `u32`
//! values `x, y`, then outputs `(y << 32) | x`. To implement `next_u32`
//! from `next_u64` in little-endian order, one should use `next_u64() as u32`.
//!
//! Byte-swapping (like the std `to_le` functions) is only needed to convert
//! to/from byte sequences, and since its purpose is reproducibility,
//! non-reproducible sources (e.g. `OsRng`) need not bother with it.

use core::convert::AsRef;
use core::intrinsics::transmute;
use core::ptr::copy_nonoverlapping;
use core::{fmt, slice};
use core::cmp::min;
use core::mem::size_of;
use {RngCore, BlockRngCore, CryptoRng, SeedableRng, Error};

#[cfg(feature="serde1")] use serde::{Serialize, Deserialize};

/// Implement `next_u64` via `next_u32`, little-endian order.
pub fn next_u64_via_u32<R: RngCore + ?Sized>(rng: &mut R) -> u64 {
    // Use LE; we explicitly generate one value before the next.
    let x = u64::from(rng.next_u32());
    let y = u64::from(rng.next_u32());
    (y << 32) | x
}

/// Implement `fill_bytes` via `next_u64` and `next_u32`, little-endian order.
///
/// The fastest way to fill a slice is usually to work as long as possible with
/// integers. That is why this method mostly uses `next_u64`, and only when
/// there are 4 or less bytes remaining at the end of the slice it uses
/// `next_u32` once.
pub fn fill_bytes_via_next<R: RngCore + ?Sized>(rng: &mut R, dest: &mut [u8]) {
    let mut left = dest;
    while left.len() >= 8 {
        let (l, r) = {left}.split_at_mut(8);
        left = r;
        let chunk: [u8; 8] = unsafe {
            transmute(rng.next_u64().to_le())
        };
        l.copy_from_slice(&chunk);
    }
    let n = left.len();
    if n > 4 {
        let chunk: [u8; 8] = unsafe {
            transmute(rng.next_u64().to_le())
        };
        left.copy_from_slice(&chunk[..n]);
    } else if n > 0 {
        let chunk: [u8; 4] = unsafe {
            transmute(rng.next_u32().to_le())
        };
        left.copy_from_slice(&chunk[..n]);
    }
}

macro_rules! impl_uint_from_fill {
    ($rng:expr, $ty:ty, $N:expr) => ({
        debug_assert!($N == size_of::<$ty>());

        let mut int: $ty = 0;
        unsafe {
            let ptr = &mut int as *mut $ty as *mut u8;
            let slice = slice::from_raw_parts_mut(ptr, $N);
            $rng.fill_bytes(slice);
        }
        int
    });
}

macro_rules! fill_via_chunks {
    ($src:expr, $dst:expr, $ty:ty, $size:expr) => ({
        let chunk_size_u8 = min($src.len() * $size, $dst.len());
        let chunk_size = (chunk_size_u8 + $size - 1) / $size;
        if cfg!(target_endian="little") {
            unsafe {
                copy_nonoverlapping(
                    $src.as_ptr() as *const u8,
                    $dst.as_mut_ptr(),
                    chunk_size_u8);
            }
        } else {
            for (&n, chunk) in $src.iter().zip($dst.chunks_mut($size)) {
                let tmp = n.to_le();
                let src_ptr = &tmp as *const $ty as *const u8;
                unsafe {
                    copy_nonoverlapping(src_ptr,
                                        chunk.as_mut_ptr(),
                                        chunk.len());
                }
            }
        }

        (chunk_size, chunk_size_u8)
    });
}

/// Implement `fill_bytes` by reading chunks from the output buffer of a block
/// based RNG.
///
/// The return values are `(consumed_u32, filled_u8)`.
///
/// `filled_u8` is the number of filled bytes in `dest`, which may be less than
/// the length of `dest`.
/// `consumed_u32` is the number of words consumed from `src`, which is the same
/// as `filled_u8 / 4` rounded up.
///
/// # Example
/// (from `IsaacRng`)
///
/// ```rust,ignore
/// fn fill_bytes(&mut self, dest: &mut [u8]) {
///     let mut read_len = 0;
///     while read_len < dest.len() {
///         if self.index >= self.rsl.len() {
///             self.isaac();
///         }
///
///         let (consumed_u32, filled_u8) =
///             impls::fill_via_u32_chunks(&mut self.rsl[self.index..],
///                                        &mut dest[read_len..]);
///
///         self.index += consumed_u32;
///         read_len += filled_u8;
///     }
/// }
/// ```
pub fn fill_via_u32_chunks(src: &[u32], dest: &mut [u8]) -> (usize, usize) {
    fill_via_chunks!(src, dest, u32, 4)
}

/// Implement `fill_bytes` by reading chunks from the output buffer of a block
/// based RNG.
///
/// The return values are `(consumed_u64, filled_u8)`.
/// `filled_u8` is the number of filled bytes in `dest`, which may be less than
/// the length of `dest`.
/// `consumed_u64` is the number of words consumed from `src`, which is the same
/// as `filled_u8 / 8` rounded up.
///
/// See `fill_via_u32_chunks` for an example.
pub fn fill_via_u64_chunks(src: &[u64], dest: &mut [u8]) -> (usize, usize) {
    fill_via_chunks!(src, dest, u64, 8)
}

/// Implement `next_u32` via `fill_bytes`, little-endian order.
pub fn next_u32_via_fill<R: RngCore + ?Sized>(rng: &mut R) -> u32 {
    impl_uint_from_fill!(rng, u32, 4)
}

/// Implement `next_u64` via `fill_bytes`, little-endian order.
pub fn next_u64_via_fill<R: RngCore + ?Sized>(rng: &mut R) -> u64 {
    impl_uint_from_fill!(rng, u64, 8)
}

/// Wrapper around PRNGs that implement [`BlockRngCore`] to keep a results
/// buffer and offer the methods from [`RngCore`].
///
/// `BlockRng` has heavily optimized implementations of the [`RngCore`] methods
/// reading values from the results buffer, as well as
/// calling `BlockRngCore::generate` directly on the output array when
/// `fill_bytes` / `try_fill_bytes` is called on a large array. These methods
/// also handle the bookkeeping of when to generate a new batch of values.
/// No generated values are ever thown away.
///
/// Currently `BlockRng` only implements `RngCore` for buffers which are slices
/// of `u32` elements; this may be extended to other types in the future.
///
/// For easy initialization `BlockRng` also implements [`SeedableRng`].
///
/// [`BlockRngCore`]: ../BlockRngCore.t.html
/// [`RngCore`]: ../RngCore.t.html
/// [`SeedableRng`]: ../SeedableRng.t.html
#[derive(Clone)]
#[cfg_attr(feature="serde1", derive(Serialize, Deserialize))]
pub struct BlockRng<R: BlockRngCore + ?Sized> {
    #[cfg_attr(feature="serde1", serde(bound(
        serialize = "R::Results: Serialize",
        deserialize = "R::Results: Deserialize<'de>")))]
    results: R::Results,
    index: usize,
    core: R,
}

// Custom Debug implementation that does not expose the contents of `results`.
impl<R: BlockRngCore + fmt::Debug> fmt::Debug for BlockRng<R> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("BlockRng")
           .field("core", &self.core)
           .field("result_len", &self.results.as_ref().len())
           .field("index", &self.index)
           .finish()
    }
}

impl<R: BlockRngCore> BlockRng<R> {
    /// Create a new `BlockRng` from an existing RNG implementing
    /// `BlockRngCore`. Results will be generated on first use.
    pub fn new(core: R) -> BlockRng<R>{
        let results_empty = R::Results::default();
        BlockRng {
            core,
            index: results_empty.as_ref().len(),
            results: results_empty,
        }
    }

    /// Return a reference the wrapped `BlockRngCore`.
    pub fn inner(&self) -> &R {
        &self.core
    }

    /// Return a mutable reference the wrapped `BlockRngCore`.
    pub fn inner_mut(&mut self) -> &mut R {
        &mut self.core
    }

    // Reset the number of available results.
    // This will force a new set of results to be generated on next use.
    pub fn reset(&mut self) {
        self.index = self.results.as_ref().len();
    }
}

impl<R: BlockRngCore<Item=u32>> RngCore for BlockRng<R>
where <R as BlockRngCore>::Results: AsRef<[u32]>
{
    #[inline(always)]
    fn next_u32(&mut self) -> u32 {
        if self.index >= self.results.as_ref().len() {
            self.core.generate(&mut self.results);
            self.index = 0;
        }

        let value = self.results.as_ref()[self.index];
        self.index += 1;
        value
    }

    #[inline(always)]
    fn next_u64(&mut self) -> u64 {
        let read_u64 = |results: &[u32], index| {
            if cfg!(any(target_arch = "x86", target_arch = "x86_64")) {
                // requires little-endian CPU supporting unaligned reads:
                unsafe { *(&results[index] as *const u32 as *const u64) }
            } else {
                let x = u64::from(results[index]);
                let y = u64::from(results[index + 1]);
                (y << 32) | x
            }
        };

        let len = self.results.as_ref().len();

        let index = self.index;
        if index < len-1 {
            self.index += 2;
            // Read an u64 from the current index
            read_u64(self.results.as_ref(), index)
        } else if index >= len {
            self.core.generate(&mut self.results);
            self.index = 2;
            read_u64(self.results.as_ref(), 0)
        } else {
            let x = u64::from(self.results.as_ref()[len-1]);
            self.core.generate(&mut self.results);
            self.index = 1;
            let y = u64::from(self.results.as_ref()[0]);
            (y << 32) | x
        }
    }

    // As an optimization we try to write directly into the output buffer.
    // This is only enabled for little-endian platforms where unaligned writes
    // are known to be safe and fast.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        let mut filled = 0;

        // Continue filling from the current set of results
        if self.index < self.results.as_ref().len() {
            let (consumed_u32, filled_u8) =
                fill_via_u32_chunks(&self.results.as_ref()[self.index..],
                                    dest);

            self.index += consumed_u32;
            filled += filled_u8;
        }

        let len_remainder =
            (dest.len() - filled) % (self.results.as_ref().len() * 4);
        let end_direct = dest.len() - len_remainder;

        while filled < end_direct {
            let dest_u32: &mut R::Results = unsafe {
                &mut *(dest[filled..].as_mut_ptr() as
                *mut <R as BlockRngCore>::Results)
            };
            self.core.generate(dest_u32);
            filled += self.results.as_ref().len() * 4;
        }
        self.index = self.results.as_ref().len();

        if len_remainder > 0 {
            self.core.generate(&mut self.results);
            let (consumed_u32, _) =
                fill_via_u32_chunks(self.results.as_ref(),
                                    &mut dest[filled..]);

            self.index = consumed_u32;
        }
    }

    #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        let mut read_len = 0;
        while read_len < dest.len() {
            if self.index >= self.results.as_ref().len() {
                self.core.generate(&mut self.results);
                self.index = 0;
            }
            let (consumed_u32, filled_u8) =
                fill_via_u32_chunks(&self.results.as_ref()[self.index..],
                                    &mut dest[read_len..]);

            self.index += consumed_u32;
            read_len += filled_u8;
        }
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

impl<R: BlockRngCore + SeedableRng> SeedableRng for BlockRng<R> {
    type Seed = R::Seed;

    fn from_seed(seed: Self::Seed) -> Self {
        Self::new(R::from_seed(seed))
    }

    fn from_rng<S: RngCore>(rng: S) -> Result<Self, Error> {
        Ok(Self::new(R::from_rng(rng)?))
    }
}



/// Wrapper around PRNGs that implement [`BlockRngCore`] to keep a results
/// buffer and offer the methods from [`RngCore`].
///
/// This is similar to [`BlockRng`], but specialized for algorithms that operate
/// on `u64` values.
///
/// [`BlockRngCore`]: ../BlockRngCore.t.html
/// [`RngCore`]: ../RngCore.t.html
/// [`BlockRng`]: struct.BlockRng.html
#[derive(Clone)]
#[cfg_attr(feature="serde1", derive(Serialize, Deserialize))]
pub struct BlockRng64<R: BlockRngCore + ?Sized> {
    #[cfg_attr(feature="serde1", serde(bound(
        serialize = "R::Results: Serialize",
        deserialize = "R::Results: Deserialize<'de>")))]
    results: R::Results,
    index: usize,
    half_used: bool, // true if only half of the previous result is used
    core: R,
}

// Custom Debug implementation that does not expose the contents of `results`.
impl<R: BlockRngCore + fmt::Debug> fmt::Debug for BlockRng64<R> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("BlockRng64")
           .field("core", &self.core)
           .field("result_len", &self.results.as_ref().len())
           .field("index", &self.index)
           .field("half_used", &self.half_used)
           .finish()
    }
}

impl<R: BlockRngCore> BlockRng64<R> {
    /// Create a new `BlockRng` from an existing RNG implementing
    /// `BlockRngCore`. Results will be generated on first use.
    pub fn new(core: R) -> BlockRng64<R>{
        let results_empty = R::Results::default();
        BlockRng64 {
            core,
            index: results_empty.as_ref().len(),
            half_used: false,
            results: results_empty,
        }
    }

    /// Return a mutable reference the wrapped `BlockRngCore`.
    pub fn inner(&mut self) -> &mut R {
        &mut self.core
    }

    // Reset the number of available results.
    // This will force a new set of results to be generated on next use.
    pub fn reset(&mut self) {
        self.index = self.results.as_ref().len();
    }
}

impl<R: BlockRngCore<Item=u64>> RngCore for BlockRng64<R>
where <R as BlockRngCore>::Results: AsRef<[u64]>
{
    #[inline(always)]
    fn next_u32(&mut self) -> u32 {
        let mut index = self.index * 2 - self.half_used as usize;
        if index >= self.results.as_ref().len() * 2 {
            self.core.generate(&mut self.results);
            self.index = 0;
            // `self.half_used` is by definition `false`
            self.half_used = false;
            index = 0;
        }

        self.half_used = !self.half_used;
        self.index += self.half_used as usize;

        // Index as if this is a u32 slice.
        unsafe {
            let results =
                &*(self.results.as_ref() as *const [u64] as *const [u32]);
            if cfg!(target_endian = "little") {
                *results.get_unchecked(index)
            } else {
                *results.get_unchecked(index ^ 1)
            }
        }
    }

    #[inline(always)]
    fn next_u64(&mut self) -> u64 {
        if self.index >= self.results.as_ref().len() {
            self.core.generate(&mut self.results);
            self.index = 0;
        }

        let value = self.results.as_ref()[self.index];
        self.index += 1;
        self.half_used = false;
        value
    }

    // As an optimization we try to write directly into the output buffer.
    // This is only enabled for little-endian platforms where unaligned writes
    // are known to be safe and fast.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        let mut filled = 0;
        self.half_used = false;

        // Continue filling from the current set of results
        if self.index < self.results.as_ref().len() {
            let (consumed_u64, filled_u8) =
                fill_via_u64_chunks(&self.results.as_ref()[self.index..],
                                    dest);

            self.index += consumed_u64;
            filled += filled_u8;
        }

        let len_remainder =
            (dest.len() - filled) % (self.results.as_ref().len() * 8);
        let end_direct = dest.len() - len_remainder;

        while filled < end_direct {
            let dest_u64: &mut R::Results = unsafe {
                ::core::mem::transmute(dest[filled..].as_mut_ptr())
            };
            self.core.generate(dest_u64);
            filled += self.results.as_ref().len() * 8;
        }
        self.index = self.results.as_ref().len();

        if len_remainder > 0 {
            self.core.generate(&mut self.results);
            let (consumed_u64, _) =
                fill_via_u64_chunks(&mut self.results.as_ref(),
                                    &mut dest[filled..]);

            self.index = consumed_u64;
        }
    }

    #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        let mut read_len = 0;
        self.half_used = false;
        while read_len < dest.len() {
            if self.index as usize >= self.results.as_ref().len() {
                self.core.generate(&mut self.results);
                self.index = 0;
            }

            let (consumed_u64, filled_u8) =
                fill_via_u64_chunks(&self.results.as_ref()[self.index as usize..],
                                    &mut dest[read_len..]);

            self.index += consumed_u64;
            read_len += filled_u8;
        }
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        Ok(self.fill_bytes(dest))
    }
}

impl<R: BlockRngCore + SeedableRng> SeedableRng for BlockRng64<R> {
    type Seed = R::Seed;

    fn from_seed(seed: Self::Seed) -> Self {
        Self::new(R::from_seed(seed))
    }

    fn from_rng<S: RngCore>(rng: S) -> Result<Self, Error> {
        Ok(Self::new(R::from_rng(rng)?))
    }
}

impl<R: BlockRngCore + CryptoRng> CryptoRng for BlockRng<R> {}

// TODO: implement tests for the above
