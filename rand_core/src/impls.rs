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
//! 
//! Missing from here are implementations of `next_u*` in terms of `try_fill`.
//! Currently `OsRng` handles these implementations itself.
//! TODO: should we add more implementations?

use core::intrinsics::transmute;
use {Rng, Result};

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

macro_rules! try_fill_via {
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
        Ok(())
    }}
}

/// Implement `try_fill` via `next_u32`, little-endian order.
pub fn try_fill_via_u32<R: Rng+?Sized>(rng: &mut R, dest: &mut [u8]) -> Result<()> {
    try_fill_via!(rng, next_u32, 4, dest)
}

/// Implement `try_fill` via `next_u64`, little-endian order.
pub fn try_fill_via_u64<R: Rng+?Sized>(rng: &mut R, dest: &mut [u8]) -> Result<()> {
    try_fill_via!(rng, next_u64, 8, dest)
}

/// Implement `try_fill` via `next_u128`, little-endian order.
#[cfg(feature = "i128_support")]
pub fn try_fill_via_u128<R: Rng+?Sized>(rng: &mut R, dest: &mut [u8]) -> Result<()> {
    try_fill_via!(rng, next_u128, 16, dest)
}

// TODO: implement tests for the above
