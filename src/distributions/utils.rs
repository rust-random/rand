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


/// Helper trait when dealing with scalar and SIMD floating point types.
pub(crate) trait FloatSIMDUtils {
    // `PartialOrd` for vectors compares lexicographically. We want to compare all
    // the individual SIMD lanes instead, and get the combined result over all
    // lanes. This is possible using something like `a.lt(b).all()`, but we
    // implement it as a trait so we can write the same code for `f32` and `f64`.
    // Only the comparison functions we need are implemented.
    fn all_lt(self, other: Self) -> bool;
    fn all_le(self, other: Self) -> bool;
    fn all_finite(self) -> bool;

    type Mask;
    fn finite_mask(self) -> Self::Mask;
    fn gt_mask(self, other: Self) -> Self::Mask;
    fn ge_mask(self, other: Self) -> Self::Mask;

    // Decrease all lanes where the mask is `true` to the next lower value
    // representable by the floating-point type. At least one of the lanes
    // must be set.
    fn decrease_masked(self, mask: Self::Mask) -> Self;

    // Convert from int value. Conversion is done while retaining the numerical
    // value, not by retaining the binary representation.
    type UInt;
    fn cast_from_int(i: Self::UInt) -> Self;
}

/// Implement functions available in std builds but missing from core primitives
#[cfg(not(std))]
pub(crate) trait Float : Sized {
    type Bits;

    fn is_nan(self) -> bool;
    fn is_infinite(self) -> bool;
    fn is_finite(self) -> bool;
    fn to_bits(self) -> Self::Bits;
    fn from_bits(v: Self::Bits) -> Self;
}

/// Implement functions on f32/f64 to give them APIs similar to SIMD types
pub(crate) trait FloatAsSIMD : Sized {
    #[inline(always)]
    fn lanes() -> usize { 1 }
    #[inline(always)]
    fn splat(scalar: Self) -> Self { scalar }
    #[inline(always)]
    fn extract(self, index: usize) -> Self { debug_assert_eq!(index, 0); self }
    #[inline(always)]
    fn replace(self, index: usize, new_value: Self) -> Self { debug_assert_eq!(index, 0); new_value }
}

pub(crate) trait BoolAsSIMD : Sized {
    fn any(self) -> bool;
    fn all(self) -> bool;
    fn none(self) -> bool;
}

impl BoolAsSIMD for bool {
    #[inline(always)]
    fn any(self) -> bool { self }
    #[inline(always)]
    fn all(self) -> bool { self }
    #[inline(always)]
    fn none(self) -> bool { !self }
}

macro_rules! scalar_float_impl {
    ($ty:ident, $uty:ident) => {
        #[cfg(not(std))]
        impl Float for $ty {
            type Bits = $uty;

            #[inline]
            fn is_nan(self) -> bool {
                self != self
            }

            #[inline]
            fn is_infinite(self) -> bool {
                self == ::core::$ty::INFINITY || self == ::core::$ty::NEG_INFINITY
            }

            #[inline]
            fn is_finite(self) -> bool {
                !(self.is_nan() || self.is_infinite())
            }

            #[inline]
            fn to_bits(self) -> Self::Bits {
                unsafe { ::core::mem::transmute(self) }
            }

            #[inline]
            fn from_bits(v: Self::Bits) -> Self {
                // It turns out the safety issues with sNaN were overblown! Hooray!
                unsafe { ::core::mem::transmute(v) }
            }
        }

        impl FloatSIMDUtils for $ty {
            type Mask = bool;
            #[inline(always)]
            fn all_lt(self, other: Self) -> bool { self < other }
            #[inline(always)]
            fn all_le(self, other: Self) -> bool { self <= other }
            #[inline(always)]
            fn all_finite(self) -> bool { self.is_finite() }
            #[inline(always)]
            fn finite_mask(self) -> Self::Mask { self.is_finite() }
            #[inline(always)]
            fn gt_mask(self, other: Self) -> Self::Mask { self > other }
            #[inline(always)]
            fn ge_mask(self, other: Self) -> Self::Mask { self >= other }
            #[inline(always)]
            fn decrease_masked(self, mask: Self::Mask) -> Self {
                debug_assert!(mask, "At least one lane must be set");
                <$ty>::from_bits(self.to_bits() - 1)
            }
            type UInt = $uty;
            fn cast_from_int(i: Self::UInt) -> Self { i as $ty }
        }

        impl FloatAsSIMD for $ty {}
    }
}

scalar_float_impl!(f32, u32);
scalar_float_impl!(f64, u64);


#[cfg(feature="simd_support")]
macro_rules! simd_impl {
    ($ty:ident, $f_scalar:ident, $mty:ident, $uty:ident) => {
        impl FloatSIMDUtils for $ty {
            type Mask = $mty;
            #[inline(always)]
            fn all_lt(self, other: Self) -> bool { self.lt(other).all() }
            #[inline(always)]
            fn all_le(self, other: Self) -> bool { self.le(other).all() }
            #[inline(always)]
            fn all_finite(self) -> bool { self.finite_mask().all() }
            #[inline(always)]
            fn finite_mask(self) -> Self::Mask {
                // This can possibly be done faster by checking bit patterns
                let neg_inf = $ty::splat(::core::$f_scalar::NEG_INFINITY);
                let pos_inf = $ty::splat(::core::$f_scalar::INFINITY);
                self.gt(neg_inf) & self.lt(pos_inf)
            }
            #[inline(always)]
            fn gt_mask(self, other: Self) -> Self::Mask { self.gt(other) }
            #[inline(always)]
            fn ge_mask(self, other: Self) -> Self::Mask { self.ge(other) }
            #[inline(always)]
            fn decrease_masked(self, mask: Self::Mask) -> Self {
                // Casting a mask into ints will produce all bits set for
                // true, and 0 for false. Adding that to the binary
                // representation of a float means subtracting one from
                // the binary representation, resulting in the next lower
                // value representable by $ty. This works even when the
                // current value is infinity.
                debug_assert!(mask.any(), "At least one lane must be set");
                <$ty>::from_bits(<$uty>::from_bits(self) + <$uty>::from_bits(mask))
            }
            type UInt = $uty;
            fn cast_from_int(i: Self::UInt) -> Self { $ty::from(i) }
        }
    }
}

#[cfg(feature="simd_support")] simd_impl! { f32x2, f32, m32x2, u32x2 }
#[cfg(feature="simd_support")] simd_impl! { f32x4, f32, m32x4, u32x4 }
#[cfg(feature="simd_support")] simd_impl! { f32x8, f32, m32x8, u32x8 }
#[cfg(feature="simd_support")] simd_impl! { f32x16, f32, m1x16, u32x16 }
#[cfg(feature="simd_support")] simd_impl! { f64x2, f64, m64x2, u64x2 }
#[cfg(feature="simd_support")] simd_impl! { f64x4, f64, m64x4, u64x4 }
#[cfg(feature="simd_support")] simd_impl! { f64x8, f64, m1x8, u64x8 }
