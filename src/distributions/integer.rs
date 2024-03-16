// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The implementations of the `Standard` distribution for integer types.

use crate::distributions::{Distribution, Standard};
use crate::Rng;
#[cfg(all(target_arch = "x86", feature = "simd_support"))]
use core::arch::x86::__m512i;
#[cfg(target_arch = "x86")]
use core::arch::x86::{__m128i, __m256i};
#[cfg(all(target_arch = "x86_64", feature = "simd_support"))]
use core::arch::x86_64::__m512i;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::{__m128i, __m256i};
use core::num::{
    NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize,NonZeroU128,
    NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize,NonZeroI128
};
#[cfg(feature = "simd_support")] use core::simd::*;
use core::mem;

impl Distribution<u8> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u8 {
        rng.next_u32() as u8
    }
}

impl Distribution<u16> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u16 {
        rng.next_u32() as u16
    }
}

impl Distribution<u32> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u32 {
        rng.next_u32()
    }
}

impl Distribution<u64> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u64 {
        rng.next_u64()
    }
}

impl Distribution<u128> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u128 {
        // Use LE; we explicitly generate one value before the next.
        let x = u128::from(rng.next_u64());
        let y = u128::from(rng.next_u64());
        (y << 64) | x
    }
}

impl Distribution<usize> for Standard {
    #[inline]
    #[cfg(any(target_pointer_width = "32", target_pointer_width = "16"))]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> usize {
        rng.next_u32() as usize
    }

    #[inline]
    #[cfg(target_pointer_width = "64")]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> usize {
        rng.next_u64() as usize
    }
}

macro_rules! impl_int_from_uint {
    ($ty:ty, $uty:ty) => {
        impl Distribution<$ty> for Standard {
            #[inline]
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                rng.gen::<$uty>() as $ty
            }
        }
    };
}

impl_int_from_uint! { i8, u8 }
impl_int_from_uint! { i16, u16 }
impl_int_from_uint! { i32, u32 }
impl_int_from_uint! { i64, u64 }
impl_int_from_uint! { i128, u128 }
impl_int_from_uint! { isize, usize }

macro_rules! impl_nzint {
    ($ty:ty, $new:path) => {
        impl Distribution<$ty> for Standard {
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                loop {
                    if let Some(nz) = $new(rng.gen()) {
                        break nz;
                    }
                }
            }
        }
    };
}

impl_nzint!(NonZeroU8, NonZeroU8::new);
impl_nzint!(NonZeroU16, NonZeroU16::new);
impl_nzint!(NonZeroU32, NonZeroU32::new);
impl_nzint!(NonZeroU64, NonZeroU64::new);
impl_nzint!(NonZeroU128, NonZeroU128::new);
impl_nzint!(NonZeroUsize, NonZeroUsize::new);

impl_nzint!(NonZeroI8, NonZeroI8::new);
impl_nzint!(NonZeroI16, NonZeroI16::new);
impl_nzint!(NonZeroI32, NonZeroI32::new);
impl_nzint!(NonZeroI64, NonZeroI64::new);
impl_nzint!(NonZeroI128, NonZeroI128::new);
impl_nzint!(NonZeroIsize, NonZeroIsize::new);

macro_rules! x86_intrinsic_impl {
    ($meta:meta, $($intrinsic:ident),+) => {$(
        #[cfg($meta)]
        #[cfg_attr(doc_cfg, doc(cfg($meta)))]
        impl Distribution<$intrinsic> for Standard {
            #[inline]
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $intrinsic {
                // On proper hardware, this should compile to SIMD instructions
                // Verified on x86 Haswell with __m128i, __m256i
                let mut buf = [0_u8; mem::size_of::<$intrinsic>()];
                rng.fill_bytes(&mut buf);
                // x86 is little endian so no need for conversion
                zerocopy::transmute!(buf)
            }
        }
    )+};
}

#[cfg(feature = "simd_support")]
macro_rules! simd_impl {
    ($($ty:ty),+) => {$(
        /// Requires nightly Rust and the [`simd_support`] feature
        ///
        /// [`simd_support`]: https://github.com/rust-random/rand#crate-features
        #[cfg(feature = "simd_support")]
        // TODO: as doc_cfg/doc_auto_cfg mature ensure they catch this
        #[cfg_attr(doc_cfg, doc(cfg(feature = "simd_support")))]
        impl<const LANES: usize> Distribution<Simd<$ty, LANES>> for Standard
        where
            LaneCount<LANES>: SupportedLaneCount,
        {
            #[inline]
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Simd<$ty, LANES> {
                let mut vec = Simd::default();
                rng.fill(vec.as_mut_array().as_mut_slice());
                vec
            }
        }
    )+};
}

#[cfg(feature = "simd_support")]
simd_impl!(u8, i8, u16, i16, u32, i32, u64, i64, usize, isize);

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
x86_intrinsic_impl!(
    any(target_arch = "x86", target_arch = "x86_64"),
    __m128i,
    __m256i
);
#[cfg(all(
    any(target_arch = "x86", target_arch = "x86_64"),
    feature = "simd_support"
))]
x86_intrinsic_impl!(
    all(
        any(target_arch = "x86", target_arch = "x86_64"),
        feature = "simd_support"
    ),
    __m512i
);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_integers() {
        let mut rng = crate::test::rng(806);

        rng.sample::<isize, _>(Standard);
        rng.sample::<i8, _>(Standard);
        rng.sample::<i16, _>(Standard);
        rng.sample::<i32, _>(Standard);
        rng.sample::<i64, _>(Standard);
        rng.sample::<i128, _>(Standard);

        rng.sample::<usize, _>(Standard);
        rng.sample::<u8, _>(Standard);
        rng.sample::<u16, _>(Standard);
        rng.sample::<u32, _>(Standard);
        rng.sample::<u64, _>(Standard);
        rng.sample::<u128, _>(Standard);
    }

    #[test]
    fn value_stability() {
        fn test_samples<T: Copy + core::fmt::Debug + PartialEq>(zero: T, expected: &[T])
        where Standard: Distribution<T> {
            let mut rng = crate::test::rng(807);
            let mut buf = [zero; 3];
            for x in &mut buf {
                *x = rng.sample(Standard);
            }
            assert_eq!(&buf, expected);
        }

        test_samples(0u8, &[9, 247, 111]);
        test_samples(0u16, &[32265, 42999, 38255]);
        test_samples(0u32, &[2220326409, 2575017975, 2018088303]);
        test_samples(0u64, &[
            11059617991457472009,
            16096616328739788143,
            1487364411147516184,
        ]);
        test_samples(0u128, &[
            296930161868957086625409848350820761097,
            145644820879247630242265036535529306392,
            111087889832015897993126088499035356354,
        ]);
        #[cfg(any(target_pointer_width = "32", target_pointer_width = "16"))]
        test_samples(0usize, &[2220326409, 2575017975, 2018088303]);
        #[cfg(target_pointer_width = "64")]
        test_samples(0usize, &[
            11059617991457472009,
            16096616328739788143,
            1487364411147516184,
        ]);

        test_samples(0i8, &[9, -9, 111]);
        // Skip further i* types: they are simple reinterpretation of u* samples

        #[cfg(feature = "simd_support")]
        {
            // We only test a sub-set of types here and make assumptions about the rest.

            test_samples(u8x4::default(), &[
                u8x4::from([9, 126, 87, 132]),
                u8x4::from([247, 167, 123, 153]),
                u8x4::from([111, 149, 73, 120]),
            ]);
            test_samples(u8x8::default(), &[
                u8x8::from([9, 126, 87, 132, 247, 167, 123, 153]),
                u8x8::from([111, 149, 73, 120, 68, 171, 98, 223]),
                u8x8::from([24, 121, 1, 50, 13, 46, 164, 20]),
            ]);

            test_samples(i64x8::default(), &[
                i64x8::from([
                    -7387126082252079607,
                    -2350127744969763473,
                    1487364411147516184,
                    7895421560427121838,
                    602190064936008898,
                    6022086574635100741,
                    -5080089175222015595,
                    -4066367846667249123,
                ]),
                i64x8::from([
                    9180885022207963908,
                    3095981199532211089,
                    6586075293021332726,
                    419343203796414657,
                    3186951873057035255,
                    5287129228749947252,
                    444726432079249540,
                    -1587028029513790706,
                ]),
                i64x8::from([
                    6075236523189346388,
                    1351763722368165432,
                    -6192309979959753740,
                    -7697775502176768592,
                    -4482022114172078123,
                    7522501477800909500,
                    -1837258847956201231,
                    -586926753024886735,
                ]),
            ]);
        }
    }
}
