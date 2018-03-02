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

use core::intrinsics::transmute;
use core::ptr::copy_nonoverlapping;
use core::{fmt, slice};
use core::cmp::min;
use core::mem::size_of;
use {RngCore, BlockRngCore, CryptoRng, SeedableRng, Error};

/// Implement `next_u64` via `next_u32`, little-endian order.
pub fn next_u64_via_u32<R: RngCore + ?Sized>(rng: &mut R) -> u64 {
    // Use LE; we explicitly generate one value before the next.
    let x = rng.next_u32() as u64;
    let y = rng.next_u32() as u64;
    (y << 32) | x
}

macro_rules! fill_bytes_via {
    ($rng:ident, $next_u:ident, $BYTES:expr, $dest:ident) => {{
        let mut left = $dest;
        while left.len() >= $BYTES {
            let (l, r) = {left}.split_at_mut($BYTES);
            left = r;
            let chunk: [u8; $BYTES] = unsafe {
                transmute($rng.$next_u().to_le())
            };
            l.copy_from_slice(&chunk);
        }
        let n = left.len();
        if n > 0 {
            let chunk: [u8; $BYTES] = unsafe {
                transmute($rng.$next_u().to_le())
            };
            left.copy_from_slice(&chunk[..n]);
        }
    }}
}

/// Implement `fill_bytes` via `next_u32`, little-endian order.
pub fn fill_bytes_via_u32<R: RngCore + ?Sized>(rng: &mut R, dest: &mut [u8]) {
    fill_bytes_via!(rng, next_u32, 4, dest)
}

/// Implement `fill_bytes` via `next_u64`, little-endian order.
pub fn fill_bytes_via_u64<R: RngCore + ?Sized>(rng: &mut R, dest: &mut [u8]) {
    fill_bytes_via!(rng, next_u64, 8, dest)
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
/// `BlockRng` has optimized methods to read from the output array that the
/// algorithm of many cryptograpic RNGs generates natively. Also they handle the
/// bookkeeping when to generate a new batch of values.
///
/// `next_u32` simply indexes the array. `next_u64` tries to read two `u32`
/// values at a time if possible, and handles edge cases like when only one
/// value is left. `try_fill_bytes` is optimized to even attempt to use the
/// [`BlockRngCore`] implementation to write the results directly to the
/// destination slice. No generated values are ever thown away.
///
/// Although `BlockCoreRng::generate` can return a `Result`, we assume all PRNGs
/// to be infallible, and for the `Result` to only have a signaling function.
/// Therefore, the error is only reported by `try_fill_bytes`, all other
/// functions squelch the error.
///
/// For easy initialization `BlockRng` also implements [`SeedableRng`].
///
/// [`BlockRngCore`]: ../BlockRngCore.t.html
/// [`RngCore`]: ../RngCore.t.html
/// [`SeedableRng`]: ../SeedableRng.t.html
#[derive(Clone)]
pub struct BlockRng<R: BlockRngCore<u32>> {
    pub core: R,
    pub results: R::Results,
    pub index: usize,
}

// Custom Debug implementation that does not expose the contents of `results`.
impl<R: BlockRngCore<u32>+fmt::Debug> fmt::Debug for BlockRng<R> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("BlockRng")
           .field("core", &self.core)
           .field("result_len", &self.results.as_ref().len())
           .field("index", &self.index)
           .finish()
    }
}

impl<R: BlockRngCore<u32>> RngCore for BlockRng<R> {
    #[inline(always)]
    fn next_u32(&mut self) -> u32 {
        if self.index >= self.results.as_ref().len() {
            let _ = self.core.generate(&mut self.results).unwrap();
            self.index = 0;
        }

        let value = self.results.as_ref()[self.index];
        self.index += 1;
        value
    }

    #[inline(always)]
    fn next_u64(&mut self) -> u64 {
        let len = self.results.as_ref().len();

        let index = self.index;
        if index < len-1 {
            self.index += 2;
            // Read an u64 from the current index
            if cfg!(any(target_arch = "x86", target_arch = "x86_64")) {
                unsafe { *(&self.results.as_ref()[index] as *const u32 as *const u64) }
            } else {
                let x = self.results.as_ref()[index] as u64;
                let y = self.results.as_ref()[index + 1] as u64;
                (y << 32) | x
            }
        } else if index >= len {
            let _ = self.core.generate(&mut self.results);
            self.index = 2;
            let x = self.results.as_ref()[0] as u64;
            let y = self.results.as_ref()[1] as u64;
            (y << 32) | x
        } else {
            let x = self.results.as_ref()[len-1] as u64;
            let _ = self.core.generate(&mut self.results);
            self.index = 1;
            let y = self.results.as_ref()[0] as u64;
            (y << 32) | x
        }
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        let _ = self.try_fill_bytes(dest);
    }

    // As an optimization we try to write directly into the output buffer.
    // This is only enabled for platforms where unaligned writes are known to
    // be safe and fast.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        let mut filled = 0;
        let mut res = Ok(());

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
        let len_direct = dest.len() - len_remainder;

        while filled < len_direct {
            let dest_u32: &mut R::Results = unsafe {
                ::core::mem::transmute(dest[filled..].as_mut_ptr())
            };
            let res2 = self.core.generate(dest_u32);
            if res2.is_err() && res.is_ok() { res = res2 };
            filled += self.results.as_ref().len() * 4;
        }
        self.index = self.results.as_ref().len();

        if len_remainder > 0 {
            let res2 = self.core.generate(&mut self.results);
            if res2.is_err() && res.is_ok() { res = res2 };

            let (consumed_u32, _) =
                fill_via_u32_chunks(&mut self.results.as_ref(),
                                    &mut dest[filled..]);

            self.index = consumed_u32;
        }
        res
    }

    #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        let mut res = Ok(());
        let mut read_len = 0;
        while read_len < dest.len() {
            if self.index >= self.results.as_ref().len() {
                let res2 = self.core.generate(&mut self.results);
                if res2.is_err() && res.is_ok() { res = res2 };
                self.index = 0;
            }
            let (consumed_u32, filled_u8) =
                fill_via_u32_chunks(&self.results.as_ref()[self.index..],
                                    &mut dest[read_len..]);

            self.index += consumed_u32;
            read_len += filled_u8;
        }
        res
    }
}

impl<R: BlockRngCore<u32> + SeedableRng> SeedableRng for BlockRng<R> {
    type Seed = R::Seed;

    fn from_seed(seed: Self::Seed) -> Self {
        let results_empty = R::Results::default();
        Self {
            core: R::from_seed(seed),
            index: results_empty.as_ref().len(), // generate on first use
            results: results_empty,
        }
    }

    fn from_rng<RNG: RngCore>(rng: &mut RNG) -> Result<Self, Error> {
        let results_empty = R::Results::default();
        Ok(Self {
            core: R::from_rng(rng)?,
            index: results_empty.as_ref().len(), // generate on first use
            results: results_empty,
        })
    }
}

impl<R: BlockRngCore<u32>+CryptoRng> CryptoRng for BlockRng<R> {}

// TODO: implement tests for the above
