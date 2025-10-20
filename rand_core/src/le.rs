// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! # Little-Endian utilities
//!
//! For cross-platform reproducibility, Little-Endian order (least-significant
//! part first) has been chosen as the standard for inter-type conversion.
//! For example, ``next_u64_via_u32`] takes `u32`
//! values `x, y`, then outputs `(y << 32) | x`.
//!
//! Byte-swapping (like the std `to_le` functions) is only needed to convert
//! to/from byte sequences, and since its purpose is reproducibility,
//! non-reproducible sources (e.g. `OsRng`) need not bother with it.
//!
//! ### Implementing [`RngCore`]
//!
//! Usually an implementation of [`RngCore`] will implement one of the three
//! methods over its internal source. The following helpers are provided for
//! the remaining implementations.
//!
//! **`fn next_u32`:**
//! -   `self.next_u64() as u32`
//! -   `(self.next_u64() >> 32) as u32`
//! -   <code>[next_u32_via_fill][](self)</code>
//!
//! **`fn next_u64`:**
//! -   <code>[next_u64_via_u32][](self)</code>
//! -   <code>[next_u64_via_fill][](self)</code>
//!
//! **`fn fill_bytes`:**
//! -   <code>[fill_bytes_via_next][](self, dest)</code>
//!
//! ### Implementing [`SeedableRng`]
//!
//! In many cases, [`SeedableRng::Seed`] must be converted to `[u32]` or
//! `[u64]`. The following helpers are provided:
//!
//! - [`read_u32_into`]
//! - [`read_u64_into`]

use crate::RngCore;
#[allow(unused)]
use crate::SeedableRng;

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
        let (l, r) = { left }.split_at_mut(8);
        left = r;
        let chunk: [u8; 8] = rng.next_u64().to_le_bytes();
        l.copy_from_slice(&chunk);
    }
    let n = left.len();
    if n > 4 {
        let chunk: [u8; 8] = rng.next_u64().to_le_bytes();
        left.copy_from_slice(&chunk[..n]);
    } else if n > 0 {
        let chunk: [u8; 4] = rng.next_u32().to_le_bytes();
        left.copy_from_slice(&chunk[..n]);
    }
}

pub(crate) trait Observable: Copy {
    type Bytes: Sized + AsRef<[u8]>;
    fn to_le_bytes(self) -> Self::Bytes;
}
impl Observable for u32 {
    type Bytes = [u8; 4];

    fn to_le_bytes(self) -> Self::Bytes {
        Self::to_le_bytes(self)
    }
}
impl Observable for u64 {
    type Bytes = [u8; 8];

    fn to_le_bytes(self) -> Self::Bytes {
        Self::to_le_bytes(self)
    }
}

/// Fill dest from src
///
/// Returns `(n, byte_len)`. `src[..n]` is consumed,
/// `dest[..byte_len]` is filled. `src[n..]` and `dest[byte_len..]` are left
/// unaltered.
pub(crate) fn fill_via_chunks<T: Observable>(src: &[T], dest: &mut [u8]) -> (usize, usize) {
    let size = core::mem::size_of::<T>();

    // Always use little endian for portability of results.

    let mut dest = dest.chunks_exact_mut(size);
    let mut src = src.iter();

    let zipped = dest.by_ref().zip(src.by_ref());
    let num_chunks = zipped.len();
    zipped.for_each(|(dest, src)| dest.copy_from_slice(src.to_le_bytes().as_ref()));

    let byte_len = num_chunks * size;
    if let Some(src) = src.next() {
        // We have consumed all full chunks of dest, but not src.
        let dest = dest.into_remainder();
        let n = dest.len();
        if n > 0 {
            dest.copy_from_slice(&src.to_le_bytes().as_ref()[..n]);
            return (num_chunks + 1, byte_len + n);
        }
    }
    (num_chunks, byte_len)
}

/// Implement `next_u32` via `fill_bytes`, little-endian order.
pub fn next_u32_via_fill<R: RngCore + ?Sized>(rng: &mut R) -> u32 {
    let mut buf = [0; 4];
    rng.fill_bytes(&mut buf);
    u32::from_le_bytes(buf)
}

/// Implement `next_u64` via `fill_bytes`, little-endian order.
pub fn next_u64_via_fill<R: RngCore + ?Sized>(rng: &mut R) -> u64 {
    let mut buf = [0; 8];
    rng.fill_bytes(&mut buf);
    u64::from_le_bytes(buf)
}

/// Fills `dst: &mut [u32]` from `src`
///
/// Reads use Little-Endian byte order, allowing portable reproduction of `dst`
/// from a byte slice.
///
/// # Panics
///
/// If `src` has insufficient length (if `src.len() < 4*dst.len()`).
#[inline]
#[track_caller]
pub fn read_u32_into(src: &[u8], dst: &mut [u32]) {
    assert!(src.len() >= 4 * dst.len());
    for (out, chunk) in dst.iter_mut().zip(src.chunks_exact(4)) {
        *out = u32::from_le_bytes(chunk.try_into().unwrap());
    }
}

/// Fills `dst: &mut [u64]` from `src`
///
/// # Panics
///
/// If `src` has insufficient length (if `src.len() < 8*dst.len()`).
#[inline]
#[track_caller]
pub fn read_u64_into(src: &[u8], dst: &mut [u64]) {
    assert!(src.len() >= 8 * dst.len());
    for (out, chunk) in dst.iter_mut().zip(src.chunks_exact(8)) {
        *out = u64::from_le_bytes(chunk.try_into().unwrap());
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_fill_via_u32_chunks() {
        let src_orig = [1u32, 2, 3];

        let src = src_orig;
        let mut dst = [0u8; 11];
        assert_eq!(fill_via_chunks(&src, &mut dst), (3, 11));
        assert_eq!(dst, [1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0]);

        let src = src_orig;
        let mut dst = [0u8; 13];
        assert_eq!(fill_via_chunks(&src, &mut dst), (3, 12));
        assert_eq!(dst, [1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0]);

        let src = src_orig;
        let mut dst = [0u8; 5];
        assert_eq!(fill_via_chunks(&src, &mut dst), (2, 5));
        assert_eq!(dst, [1, 0, 0, 0, 2]);
    }

    #[test]
    fn test_fill_via_u64_chunks() {
        let src_orig = [1u64, 2];

        let src = src_orig;
        let mut dst = [0u8; 11];
        assert_eq!(fill_via_chunks(&src, &mut dst), (2, 11));
        assert_eq!(dst, [1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0]);

        let src = src_orig;
        let mut dst = [0u8; 17];
        assert_eq!(fill_via_chunks(&src, &mut dst), (2, 16));
        assert_eq!(dst, [1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]);

        let src = src_orig;
        let mut dst = [0u8; 5];
        assert_eq!(fill_via_chunks(&src, &mut dst), (1, 5));
        assert_eq!(dst, [1, 0, 0, 0, 0]);
    }

    #[test]
    fn test_read() {
        let bytes = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];

        let mut buf = [0u32; 4];
        read_u32_into(&bytes, &mut buf);
        assert_eq!(buf[0], 0x04030201);
        assert_eq!(buf[3], 0x100F0E0D);

        let mut buf = [0u32; 3];
        read_u32_into(&bytes[1..13], &mut buf); // unaligned
        assert_eq!(buf[0], 0x05040302);
        assert_eq!(buf[2], 0x0D0C0B0A);

        let mut buf = [0u64; 2];
        read_u64_into(&bytes, &mut buf);
        assert_eq!(buf[0], 0x0807060504030201);
        assert_eq!(buf[1], 0x100F0E0D0C0B0A09);

        let mut buf = [0u64; 1];
        read_u64_into(&bytes[7..15], &mut buf); // unaligned
        assert_eq!(buf[0], 0x0F0E0D0C0B0A0908);
    }
}
