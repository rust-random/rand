// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Math helper functions

#[cfg(feature="simd_support")]
use core::simd::*;


pub trait WideningMultiply<RHS = Self> {
    type Output;

    fn wmul(self, x: RHS) -> Self::Output;
}

macro_rules! wmul_impl {
    ($ty:ty, $wide:ty, $shift:expr) => {
        impl WideningMultiply for $ty {
            type Output = ($ty, $ty);

            #[inline(always)]
            fn wmul(self, x: $ty) -> Self::Output {
                let tmp = (self as $wide) * (x as $wide);
                ((tmp >> $shift) as $ty, tmp as $ty)
            }
        }
    }
}
wmul_impl! { u8, u16, 8 }
wmul_impl! { u16, u32, 16 }
wmul_impl! { u32, u64, 32 }
#[cfg(feature = "i128_support")]
wmul_impl! { u64, u128, 64 }

// This code is a translation of the __mulddi3 function in LLVM's
// compiler-rt. It is an optimised variant of the common method
// `(a + b) * (c + d) = ac + ad + bc + bd`.
//
// For some reason LLVM can optimise the C version very well, but
// keeps shuffling registers in this Rust translation.
macro_rules! wmul_impl_large {
    ($ty:ty, $half:expr) => {
        impl WideningMultiply for $ty {
            type Output = ($ty, $ty);

            #[inline(always)]
            fn wmul(self, b: $ty) -> Self::Output {
                const LOWER_MASK: $ty = !0 >> $half;
                let mut low = (self & LOWER_MASK).wrapping_mul(b & LOWER_MASK);
                let mut t = low >> $half;
                low &= LOWER_MASK;
                t += (self >> $half).wrapping_mul(b & LOWER_MASK);
                low += (t & LOWER_MASK) << $half;
                let mut high = t >> $half;
                t = low >> $half;
                low &= LOWER_MASK;
                t += (b >> $half).wrapping_mul(self & LOWER_MASK);
                low += (t & LOWER_MASK) << $half;
                high += t >> $half;
                high += (self >> $half).wrapping_mul(b >> $half);

                (high, low)
            }
        }
    }
}
#[cfg(not(feature = "i128_support"))]
wmul_impl_large! { u64, 32 }
#[cfg(feature = "i128_support")]
wmul_impl_large! { u128, 64 }

macro_rules! wmul_impl_usize {
    ($ty:ty) => {
        impl WideningMultiply for usize {
            type Output = (usize, usize);

            #[inline(always)]
            fn wmul(self, x: usize) -> Self::Output {
                let (high, low) = (self as $ty).wmul(x as $ty);
                (high as usize, low as usize)
            }
        }
    }
}
#[cfg(target_pointer_width = "32")]
wmul_impl_usize! { u32 }
#[cfg(target_pointer_width = "64")]
wmul_impl_usize! { u64 }


pub trait CastFromInt<T> {
    fn cast_from_int(i: T) -> Self;
}

impl CastFromInt<u32> for f32 {
    fn cast_from_int(i: u32) -> Self { i as f32 }
}

impl CastFromInt<u64> for f64 {
    fn cast_from_int(i: u64) -> Self { i as f64 }
}

#[cfg(feature="simd_support")]
macro_rules! simd_float_from_int {
    ($ty:ident, $uty:ident) => {
        impl CastFromInt<$uty> for $ty {
            fn cast_from_int(i: $uty) -> Self { $ty::from(i) }
        }
    }
}

#[cfg(feature="simd_support")] simd_float_from_int! { f32x2, u32x2 }
#[cfg(feature="simd_support")] simd_float_from_int! { f32x4, u32x4 }
#[cfg(feature="simd_support")] simd_float_from_int! { f32x8, u32x8 }
#[cfg(feature="simd_support")] simd_float_from_int! { f32x16, u32x16 }
#[cfg(feature="simd_support")] simd_float_from_int! { f64x2, u64x2 }
#[cfg(feature="simd_support")] simd_float_from_int! { f64x4, u64x4 }
#[cfg(feature="simd_support")] simd_float_from_int! { f64x8, u64x8 }


/// `PartialOrd` for vectors compares lexicographically. We want natural order.
/// Only the comparison functions we need are implemented.
pub trait NaturalCompare {
    fn cmp_lt(self, other: Self) -> bool;
    fn cmp_le(self, other: Self) -> bool;
}

impl NaturalCompare for f32 {
    fn cmp_lt(self, other: Self) -> bool { self < other }
    fn cmp_le(self, other: Self) -> bool { self <= other }
}

impl NaturalCompare for f64 {
    fn cmp_lt(self, other: Self) -> bool { self < other }
    fn cmp_le(self, other: Self) -> bool { self <= other }
}

#[cfg(feature="simd_support")]
macro_rules! simd_less_then {
    ($ty:ident) => {
        impl NaturalCompare for $ty {
            fn cmp_lt(self, other: Self) -> bool { self.lt(other).all() }
            fn cmp_le(self, other: Self) -> bool { self.le(other).all() }
        }
    }
}

#[cfg(feature="simd_support")] simd_less_then! { f32x2 }
#[cfg(feature="simd_support")] simd_less_then! { f32x4 }
#[cfg(feature="simd_support")] simd_less_then! { f32x8 }
#[cfg(feature="simd_support")] simd_less_then! { f32x16 }
#[cfg(feature="simd_support")] simd_less_then! { f64x2 }
#[cfg(feature="simd_support")] simd_less_then! { f64x4 }
#[cfg(feature="simd_support")] simd_less_then! { f64x8 }
