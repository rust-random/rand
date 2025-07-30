// Copyright 2025 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! `Fill` trait

use super::RngCore;
use core::num::Wrapping;
use core::{mem, slice};

/// Support filling a slice with random data
///
/// This trait allows slices of "plain data" types to be efficiently filled
/// with random data.
///
/// Implementations are expected to be portable across machines unless
/// clearly documented otherwise (see the
/// [Chapter on Portability](https://rust-random.github.io/book/portability.html)).
/// The implementations provided achieve this by byte-swapping on big-endian
/// machines.
pub trait Fill: Sized {
    /// Fill this with random data
    fn fill_slice<R: RngCore + ?Sized>(this: &mut [Self], rng: &mut R);
}

impl Fill for u8 {
    fn fill_slice<R: RngCore + ?Sized>(this: &mut [Self], rng: &mut R) {
        rng.fill_bytes(this)
    }
}

/// Call target for unsafe macros
const unsafe fn __unsafe() {}

/// Implement `Fill` for given type `$t`.
///
/// # Safety
/// All bit patterns of `[u8; size_of::<$t>()]` must represent values of `$t`.
macro_rules! impl_fill {
    () => {};
    ($t:ty) => {{
        // Force caller to wrap with an `unsafe` block
        __unsafe();

        impl Fill for $t {
            fn fill_slice<R: RngCore + ?Sized>(this: &mut [Self], rng: &mut R) {
                if this.len() > 0 {
                    let size = mem::size_of_val(this);
                    rng.fill_bytes(
                        // SAFETY: `this` non-null and valid for reads and writes within its `size`
                        // bytes. `this` meets the alignment requirements of `&mut [u8]`.
                        // The contents of `this` are initialized. Both `[u8]` and `[$t]` are valid
                        // for all bit-patterns of their contents (note that the SAFETY requirement
                        // on callers of this macro). `this` is not borrowed.
                        unsafe {
                            slice::from_raw_parts_mut(this.as_mut_ptr()
                                as *mut u8,
                                size
                            )
                        }
                    );
                    for x in this {
                        *x = x.to_le();
                    }
                }
            }
        }

        impl Fill for Wrapping<$t> {
            fn fill_slice<R: RngCore + ?Sized>(this: &mut [Self], rng: &mut R) {
                if this.len() > 0 {
                    let size = this.len() * mem::size_of::<$t>();
                    rng.fill_bytes(
                        // SAFETY: `this` non-null and valid for reads and writes within its `size`
                        // bytes. `this` meets the alignment requirements of `&mut [u8]`.
                        // The contents of `this` are initialized. Both `[u8]` and `[$t]` are valid
                        // for all bit-patterns of their contents (note that the SAFETY requirement
                        // on callers of this macro). `this` is not borrowed.
                        unsafe {
                            slice::from_raw_parts_mut(this.as_mut_ptr()
                                as *mut u8,
                                size
                            )
                        }
                    );
                    for x in this {
                        *x = Wrapping(x.0.to_le());
                    }
                }
            }
        }}
    };
    ($t:ty, $($tt:ty,)*) => {{
        impl_fill!($t);
        // TODO: this could replace above impl once Rust #32463 is fixed
        // impl_fill!(Wrapping<$t>);
        impl_fill!($($tt,)*);
    }}
}

// SAFETY: All bit patterns of `[u8; size_of::<$t>()]` represent values of `u*`.
const _: () = unsafe { impl_fill!(u16, u32, u64, u128,) };
// SAFETY: All bit patterns of `[u8; size_of::<$t>()]` represent values of `i*`.
const _: () = unsafe { impl_fill!(i8, i16, i32, i64, i128,) };
