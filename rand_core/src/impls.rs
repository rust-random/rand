// Copyright 2013-2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Helper functions for implementing `Rng` functions.
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
use core::slice;
use core::cmp::min;
use Rng;

/// Implement `next_u64` via `next_u32`, little-endian order.
pub fn next_u64_via_u32<R: Rng+?Sized>(rng: &mut R) -> u64 {
    // Use LE; we explicitly generate one value before the next.
    let x = rng.next_u32() as u64;
    let y = rng.next_u32() as u64;
    (y << 32) | x
}

/// Implement `next_u128` via `next_u64`, little-endian order.
/// 
/// This may be used even where `next_u64` is implemented via `next_u32`.
#[cfg(feature = "i128_support")]
pub fn next_u128_via_u64<R: Rng+?Sized>(rng: &mut R) -> u128 {
    // Use LE; we explicitly generate one value before the next.
    let x = rng.next_u64() as u128;
    let y = rng.next_u64() as u128;
    (y << 64) | x
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
pub fn fill_bytes_via_u32<R: Rng+?Sized>(rng: &mut R, dest: &mut [u8]) {
    fill_bytes_via!(rng, next_u32, 4, dest)
}

/// Implement `fill_bytes` via `next_u64`, little-endian order.
pub fn fill_bytes_via_u64<R: Rng+?Sized>(rng: &mut R, dest: &mut [u8]) {
    fill_bytes_via!(rng, next_u64, 8, dest)
}

/// Implement `fill_bytes` via `next_u128`, little-endian order.
#[cfg(feature = "i128_support")]
pub fn fill_bytes_via_u128<R: Rng+?Sized>(rng: &mut R, dest: &mut [u8]) {
    fill_bytes_via!(rng, next_u128, 16, dest)
}

macro_rules! impl_uint_from_fill {
    ($self:expr, $ty:ty, $N:expr) => ({
        debug_assert!($N == ::core::mem::size_of::<$ty>());

        let mut int: $ty = 0;
        unsafe {
            let ptr = &mut int as *mut $ty as *mut u8;
            let slice = slice::from_raw_parts_mut(ptr, $N);
            $self.fill_bytes(slice);
        }
        int
    });
}

macro_rules! fill_via_chunks {
    ($src:expr, $dest:expr, $N:expr) => ({
        let chunk_size_u8 = min($src.len() * $N, $dest.len());
        let chunk_size = (chunk_size_u8 + $N - 1) / $N;

        // Convert to little-endian:
        for ref mut x in $src[0..chunk_size].iter_mut() {
            **x = (*x).to_le();
        }

        let bytes = unsafe { slice::from_raw_parts($src.as_ptr() as *const u8,
                                                   $src.len() * $N) };

        let dest_chunk = &mut $dest[0..chunk_size_u8];
        dest_chunk.copy_from_slice(&bytes[0..chunk_size_u8]);

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
/// Note that on big-endian systems values in the output buffer `src` are
/// mutated. `src[0..consumed_u32]` get converted to little-endian before
/// copying.
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
pub fn fill_via_u32_chunks(src: &mut [u32], dest: &mut [u8]) -> (usize, usize) {
    fill_via_chunks!(src, dest, 4)
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
/// Note that on big-endian systems values in the output buffer `src` are
/// mutated. `src[0..consumed_u64]` get converted to little-endian before
/// copying.
///
/// See `fill_via_u32_chunks` for an example.
pub fn fill_via_u64_chunks(src: &mut [u64], dest: &mut [u8]) -> (usize, usize) {
    fill_via_chunks!(src, dest, 8)
}

/// Implement `next_u32` via `fill_bytes`, little-endian order.
pub fn next_u32_via_fill<R: Rng+?Sized>(rng: &mut R) -> u32 {
    impl_uint_from_fill!(rng, u32, 4)
}

/// Implement `next_u64` via `fill_bytes`, little-endian order.
pub fn next_u64_via_fill<R: Rng+?Sized>(rng: &mut R) -> u64 {
    impl_uint_from_fill!(rng, u64, 8)
}

/// Implement `next_u128` via `fill_bytes`, little-endian order.
#[cfg(feature = "i128_support")]
pub fn next_u128_via_fill<R: Rng+?Sized>(rng: &mut R) -> u128 {
    impl_uint_from_fill!(rng, u128, 16)
}

// TODO: implement tests for the above
