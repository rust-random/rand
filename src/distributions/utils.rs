// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Math helper functions

#[cfg(feature = "simd_support")] use packed_simd::*;


pub(crate) trait WideningMultiply<RHS = Self> {
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
    };

    // simd bulk implementation
    ($(($ty:ident, $wide:ident),)+, $shift:expr) => {
        $(
            impl WideningMultiply for $ty {
                type Output = ($ty, $ty);

                #[inline(always)]
                fn wmul(self, x: $ty) -> Self::Output {
                    // For supported vectors, this should compile to a couple
                    // supported multiply & swizzle instructions (no actual
                    // casting).
                    // TODO: optimize
                    let y: $wide = self.cast();
                    let x: $wide = x.cast();
                    let tmp = y * x;
                    let hi: $ty = (tmp >> $shift).cast();
                    let lo: $ty = tmp.cast();
                    (hi, lo)
                }
            }
        )+
    };
}
wmul_impl! { u8, u16, 8 }
wmul_impl! { u16, u32, 16 }
wmul_impl! { u32, u64, 32 }
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
    };

    // simd bulk implementation
    (($($ty:ty,)+) $scalar:ty, $half:expr) => {
        $(
            impl WideningMultiply for $ty {
                type Output = ($ty, $ty);

                #[inline(always)]
                fn wmul(self, b: $ty) -> Self::Output {
                    // needs wrapping multiplication
                    const LOWER_MASK: $scalar = !0 >> $half;
                    let mut low = (self & LOWER_MASK) * (b & LOWER_MASK);
                    let mut t = low >> $half;
                    low &= LOWER_MASK;
                    t += (self >> $half) * (b & LOWER_MASK);
                    low += (t & LOWER_MASK) << $half;
                    let mut high = t >> $half;
                    t = low >> $half;
                    low &= LOWER_MASK;
                    t += (b >> $half) * (self & LOWER_MASK);
                    low += (t & LOWER_MASK) << $half;
                    high += t >> $half;
                    high += (self >> $half) * (b >> $half);

                    (high, low)
                }
            }
        )+
    };
}
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
    };
}
#[cfg(target_pointer_width = "16")]
wmul_impl_usize! { u16 }
#[cfg(target_pointer_width = "32")]
wmul_impl_usize! { u32 }
#[cfg(target_pointer_width = "64")]
wmul_impl_usize! { u64 }

#[cfg(feature = "simd_support")]
mod simd_wmul {
    use super::*;
    #[cfg(target_arch = "x86")] use core::arch::x86::*;
    #[cfg(target_arch = "x86_64")] use core::arch::x86_64::*;

    wmul_impl! {
        (u8x2, u16x2),
        (u8x4, u16x4),
        (u8x8, u16x8),
        (u8x16, u16x16),
        (u8x32, u16x32),,
        8
    }

    wmul_impl! { (u16x2, u32x2),, 16 }
    wmul_impl! { (u16x4, u32x4),, 16 }
    #[cfg(not(target_feature = "sse2"))]
    wmul_impl! { (u16x8, u32x8),, 16 }
    #[cfg(not(target_feature = "avx2"))]
    wmul_impl! { (u16x16, u32x16),, 16 }

    // 16-bit lane widths allow use of the x86 `mulhi` instructions, which
    // means `wmul` can be implemented with only two instructions.
    #[allow(unused_macros)]
    macro_rules! wmul_impl_16 {
        ($ty:ident, $intrinsic:ident, $mulhi:ident, $mullo:ident) => {
            impl WideningMultiply for $ty {
                type Output = ($ty, $ty);

                #[inline(always)]
                fn wmul(self, x: $ty) -> Self::Output {
                    let b = $intrinsic::from_bits(x);
                    let a = $intrinsic::from_bits(self);
                    let hi = $ty::from_bits(unsafe { $mulhi(a, b) });
                    let lo = $ty::from_bits(unsafe { $mullo(a, b) });
                    (hi, lo)
                }
            }
        };
    }

    #[cfg(target_feature = "sse2")]
    wmul_impl_16! { u16x8, __m128i, _mm_mulhi_epu16, _mm_mullo_epi16 }
    #[cfg(target_feature = "avx2")]
    wmul_impl_16! { u16x16, __m256i, _mm256_mulhi_epu16, _mm256_mullo_epi16 }
    // FIXME: there are no `__m512i` types in stdsimd yet, so `wmul::<u16x32>`
    // cannot use the same implementation.

    wmul_impl! {
        (u32x2, u64x2),
        (u32x4, u64x4),
        (u32x8, u64x8),,
        32
    }

    // TODO: optimize, this seems to seriously slow things down
    wmul_impl_large! { (u8x64,) u8, 4 }
    wmul_impl_large! { (u16x32,) u16, 8 }
    wmul_impl_large! { (u32x16,) u32, 16 }
    wmul_impl_large! { (u64x2, u64x4, u64x8,) u64, 32 }
    wmul_impl_large! { (u128x2, u128x4,) u128, 64 }

    #[cfg(target_pointer_width = "64")]
    wmul_impl_large! { (usizex2, usizex4, usizex8,) usize, 32 }
    #[cfg(target_pointer_width = "32")]
    wmul_impl_large! { (usizex2, usizex4, usizex8,) usize, 16 }
    #[cfg(target_pointer_width = "16")]
    wmul_impl_large! { (usizex2, usizex4, usizex8,) usize, 8 }
}

pub(crate) trait OverflowingAdd<T> {
    fn overflowing_add(&self, y: Self) -> (Self, T) where Self: Sized;
}

#[cfg(feature = "simd_support")]
macro_rules! impl_overflowing_add {
    ($(($ty:ty, $signed_ty:ty, $mask:ty)),+) => {$(
        #[cfg(feature = "simd_support")]
        impl OverflowingAdd<$mask> for $ty {
            #[inline]
            fn overflowing_add(&self, y: Self) -> (Self, $mask) {
                let sum = *self + y;

                let lane_bitwidth = std::mem::size_of::<$ty>() / <$ty>::lanes();
                let mask = <$ty>::splat(1 << (lane_bitwidth - 1));

                let neg_self: $signed_ty = (mask ^ *self).cast();
                let neg_sum: $signed_ty = (mask ^ sum).cast();

                let overflowed = neg_self.gt(neg_sum);

                (sum, overflowed)
            }
        }
    )+};
}

#[cfg(feature = "simd_support")]
impl_overflowing_add!(
    (u8x2, i8x2, m8x2),
    (u8x4, i8x4, m8x4),
    (u8x8, i8x8, m8x8),
    (u8x16, i8x16, m8x16),
    (u8x32, i8x32, m8x32),
    (u8x64, i8x64, m8x64),

    (u16x2, i16x2, m16x2),
    (u16x4, i16x4, m16x4),
    (u16x8, i16x8, m16x8),
    (u16x16, i16x16, m16x16),
    (u16x32, i16x32, m16x32),

    (u32x2, i32x2, m32x2),
    (u32x4, i32x4, m32x4),
    (u32x8, i32x8, m32x8),
    (u32x16, i32x16, m32x16),

    (u64x2, i64x2, m64x2),
    (u64x4, i64x4, m64x4),
    (u64x8, i64x8, m64x8),

    (u128x2, i128x2, m128x2),
    (u128x4, i128x4, m128x4)
);


#[cfg(feature = "simd_support")]
pub(crate) trait SimdCombine<T> {
    fn simd_combine(&self) -> T;
}

#[cfg(feature = "simd_support")]
macro_rules! impl_combine_2 {
    ($(($wide:ident, $short:ident)),+) => {$(
        impl SimdCombine<$wide> for [$short] {
            #[inline]
            fn simd_combine(&self) -> $wide {
                shuffle!(self[0], self[1], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15])
            }
        }
    )+};
}

#[cfg(feature = "simd_support")]
impl_combine_2!{
    (u32x16, u32x8),
    (u16x16, u16x8),
    (u8x16, u8x8)
}

#[cfg(feature = "simd_support")]
macro_rules! impl_combine_4 {
    ($(($wide:ident, $mid:ident, $short:ident)),+) => {$(
        impl SimdCombine<$wide> for [$short] {
            #[inline]
            fn simd_combine(&self) -> $wide {
                let a: $mid = self.chunks_exact(2).nth(0).unwrap().simd_combine();
                let b: $mid = self.chunks_exact(2).nth(1).unwrap().simd_combine();
                shuffle!(a, b, [
                    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
                    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31
                ])
            }
        }
    )+};
}

#[cfg(feature = "simd_support")]
impl_combine_4!{
    (u16x32, u16x16, u16x8),
    (u8x32, u8x16, u8x8)
}

#[cfg(feature = "simd_support")]
impl SimdCombine<u8x64> for [u8x8; 8] {
    #[inline]
    fn simd_combine(&self) -> u8x64 {
        let a: u8x32 = self.chunks_exact(4).nth(0).unwrap().simd_combine();
        let b: u8x32 = self.chunks_exact(4).nth(1).unwrap().simd_combine();
        shuffle!(a, b, [
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
            16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
            32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
            48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63
        ])
    }
}


#[cfg(feature = "simd_support")]
pub(crate) trait SimdSplit<T> {
    fn simd_split(&self) -> T;
}

#[cfg(feature = "simd_support")]
macro_rules! impl_split_2 {
    ($(($wide:ident, $short:ident)),+) => {$(
        impl SimdSplit<[$short; 2]> for $wide {
            #[inline]
            fn simd_split(&self) -> [$short; 2] {
                let a = shuffle!(self, [0, 1, 2, 3, 4, 5, 6, 7]);
                let b = shuffle!(self, [8, 9, 10, 11, 12, 13, 14, 15]);
                [a, b]
            }
        }
    )+};
}

#[cfg(feature = "simd_support")]
impl_split_2!{
    (u32x16, u32x8),
    (u16x16, u16x8),
    (u8x16, u8x8)
}

#[cfg(feature = "simd_support")]
macro_rules! impl_split_4 {
    ($(($wide:ident, $mid:ident, $short:ident)),+) => {$(
        impl SimdSplit<[$short; 4]> for $wide {
            #[inline]
            fn simd_split(&self) -> [$short; 4] {
                let a = shuffle!(self, [0, 1, 2, 3, 4, 5, 6, 7]);
                let b = shuffle!(self, [8, 9, 10, 11, 12, 13, 14, 15]);
                let c = shuffle!(self, [16, 17, 18, 19, 20, 21, 22, 23]);
                let d = shuffle!(self, [24, 25, 26, 27, 28, 29, 30, 31]);
                [a, b, c, d]
            }
        }
    )+};
}

#[cfg(feature = "simd_support")]
impl_split_4!{
    (u16x32, u16x16, u16x8),
    (u8x32, u8x16, u8x8)
}

#[cfg(feature = "simd_support")]
impl SimdSplit<[u8x8; 8]> for u8x64 {
    #[inline]
    fn simd_split(&self) -> [u8x8; 8] {
        let x0 = shuffle!(self, [0, 1, 2, 3, 4, 5, 6, 7]);
        let x1 = shuffle!(self, [8, 9, 10, 11, 12, 13, 14, 15]);
        let x2 = shuffle!(self, [16, 17, 18, 19, 20, 21, 22, 23]);
        let x3 = shuffle!(self, [24, 25, 26, 27, 28, 29, 30, 31]);
        let x4 = shuffle!(self, [32, 33, 34, 35, 36, 37, 38, 39]);
        let x5 = shuffle!(self, [40, 41, 42, 43, 44, 45, 46, 47]);
        let x6 = shuffle!(self, [48, 49, 50, 51, 52, 53, 54, 55]);
        let x7 = shuffle!(self, [56, 57, 58, 59, 60, 61, 62, 63]);
        [x0, x1, x2, x3, x4, x5, x6, x7]
    }
}

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
// False positive: We are following `std` here.
#[allow(clippy::wrong_self_convention)]
pub(crate) trait Float: Sized {
    fn is_nan(self) -> bool;
    fn is_infinite(self) -> bool;
    fn is_finite(self) -> bool;
}

/// Implement functions on f32/f64 to give them APIs similar to SIMD types
pub(crate) trait FloatAsSIMD: Sized {
    #[inline(always)]
    fn lanes() -> usize {
        1
    }
    #[inline(always)]
    fn splat(scalar: Self) -> Self {
        scalar
    }
    #[inline(always)]
    fn extract(self, index: usize) -> Self {
        debug_assert_eq!(index, 0);
        self
    }
    #[inline(always)]
    fn replace(self, index: usize, new_value: Self) -> Self {
        debug_assert_eq!(index, 0);
        new_value
    }
}

pub(crate) trait BoolAsSIMD: Sized {
    fn any(self) -> bool;
    fn all(self) -> bool;
    fn none(self) -> bool;
}

impl BoolAsSIMD for bool {
    #[inline(always)]
    fn any(self) -> bool {
        self
    }

    #[inline(always)]
    fn all(self) -> bool {
        self
    }

    #[inline(always)]
    fn none(self) -> bool {
        !self
    }
}

macro_rules! scalar_float_impl {
    ($ty:ident, $uty:ident) => {
        #[cfg(not(std))]
        impl Float for $ty {
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
        }

        impl FloatSIMDUtils for $ty {
            type Mask = bool;
            type UInt = $uty;

            #[inline(always)]
            fn all_lt(self, other: Self) -> bool {
                self < other
            }

            #[inline(always)]
            fn all_le(self, other: Self) -> bool {
                self <= other
            }

            #[inline(always)]
            fn all_finite(self) -> bool {
                self.is_finite()
            }

            #[inline(always)]
            fn finite_mask(self) -> Self::Mask {
                self.is_finite()
            }

            #[inline(always)]
            fn gt_mask(self, other: Self) -> Self::Mask {
                self > other
            }

            #[inline(always)]
            fn ge_mask(self, other: Self) -> Self::Mask {
                self >= other
            }

            #[inline(always)]
            fn decrease_masked(self, mask: Self::Mask) -> Self {
                debug_assert!(mask, "At least one lane must be set");
                <$ty>::from_bits(self.to_bits() - 1)
            }

            #[inline]
            fn cast_from_int(i: Self::UInt) -> Self {
                i as $ty
            }
        }

        impl FloatAsSIMD for $ty {}
    };
}

scalar_float_impl!(f32, u32);
scalar_float_impl!(f64, u64);


#[cfg(feature = "simd_support")]
macro_rules! simd_impl {
    ($ty:ident, $f_scalar:ident, $mty:ident, $uty:ident) => {
        impl FloatSIMDUtils for $ty {
            type Mask = $mty;
            type UInt = $uty;

            #[inline(always)]
            fn all_lt(self, other: Self) -> bool {
                self.lt(other).all()
            }

            #[inline(always)]
            fn all_le(self, other: Self) -> bool {
                self.le(other).all()
            }

            #[inline(always)]
            fn all_finite(self) -> bool {
                self.finite_mask().all()
            }

            #[inline(always)]
            fn finite_mask(self) -> Self::Mask {
                // This can possibly be done faster by checking bit patterns
                let neg_inf = $ty::splat(::core::$f_scalar::NEG_INFINITY);
                let pos_inf = $ty::splat(::core::$f_scalar::INFINITY);
                self.gt(neg_inf) & self.lt(pos_inf)
            }

            #[inline(always)]
            fn gt_mask(self, other: Self) -> Self::Mask {
                self.gt(other)
            }

            #[inline(always)]
            fn ge_mask(self, other: Self) -> Self::Mask {
                self.ge(other)
            }

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

            #[inline]
            fn cast_from_int(i: Self::UInt) -> Self {
                i.cast()
            }
        }
    };
}

#[cfg(feature="simd_support")] simd_impl! { f32x2, f32, m32x2, u32x2 }
#[cfg(feature="simd_support")] simd_impl! { f32x4, f32, m32x4, u32x4 }
#[cfg(feature="simd_support")] simd_impl! { f32x8, f32, m32x8, u32x8 }
#[cfg(feature="simd_support")] simd_impl! { f32x16, f32, m32x16, u32x16 }
#[cfg(feature="simd_support")] simd_impl! { f64x2, f64, m64x2, u64x2 }
#[cfg(feature="simd_support")] simd_impl! { f64x4, f64, m64x4, u64x4 }
#[cfg(feature="simd_support")] simd_impl! { f64x8, f64, m64x8, u64x8 }
