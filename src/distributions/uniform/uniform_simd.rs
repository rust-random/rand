// Copyright 2018-2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::{SampleBorrow, SampleUniform, UniformInt, UniformSampler};
use crate::distributions::utils::WideningMultiply;
use crate::Rng;
use packed_simd::*;

macro_rules! uniform_simd_int_impl {
    ($ty:ident, $unsigned:ident, $u_scalar:ident) => {
        // The "pick the largest zone that can fit in an `u32`" optimization
        // is less useful here. Multiple lanes complicate things, we don't
        // know the PRNG's minimal output size, and casting to a larger vector
        // is generally a bad idea for SIMD performance. The user can still
        // implement it manually.

        // TODO: look into `Uniform::<u32x4>::new(0u32, 100)` functionality
        //       perhaps `impl SampleUniform for $u_scalar`?
        impl SampleUniform for $ty {
            type Sampler = UniformInt<$ty>;
        }

        impl UniformSampler for UniformInt<$ty> {
            type X = $ty;

            #[inline] // if the range is constant, this helps LLVM to do the
                      // calculations at compile-time.
            fn new<B1, B2>(low_b: B1, high_b: B2) -> Self
                where B1: SampleBorrow<Self::X> + Sized,
                      B2: SampleBorrow<Self::X> + Sized
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                assert!(low.lt(high).all(), "Uniform::new called with `low >= high`");
                UniformSampler::new_inclusive(low, high - 1)
            }

            #[inline] // if the range is constant, this helps LLVM to do the
                      // calculations at compile-time.
            fn new_inclusive<B1, B2>(low_b: B1, high_b: B2) -> Self
                where B1: SampleBorrow<Self::X> + Sized,
                      B2: SampleBorrow<Self::X> + Sized
            {
                let low = *low_b.borrow();
                let high = *high_b.borrow();
                assert!(low.le(high).all(),
                        "Uniform::new_inclusive called with `low > high`");
                let unsigned_max = ::core::$u_scalar::MAX;

                // NOTE: these may need to be replaced with explicitly
                // wrapping operations if `packed_simd` changes
                let range: $unsigned = ((high - low) + 1).cast();
                // `% 0` will panic at runtime.
                let not_full_range = range.gt($unsigned::splat(0));
                // replacing 0 with `unsigned_max` allows a faster `select`
                // with bitwise OR
                let modulo = not_full_range.select(range, $unsigned::splat(unsigned_max));
                // wrapping addition
                let ints_to_reject = (unsigned_max - range + 1) % modulo;
                // When `range` is 0, `lo` of `v.wmul(range)` will always be
                // zero which means only one sample is needed.
                let zone = unsigned_max - ints_to_reject;

                UniformInt {
                    low,
                    // These are really $unsigned values, but store as $ty:
                    range: range.cast(),
                    z: zone.cast(),
                    nrmr: ((0 - range) % range).cast(),
                }
            }

            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
                let range: $unsigned = self.range.cast();
                let zone: $unsigned = self.z.cast();

                // This might seem very slow, generating a whole new
                // SIMD vector for every sample rejection. For most uses
                // though, the chance of rejection is small and provides good
                // general performance. With multiple lanes, that chance is
                // multiplied. To mitigate this, we replace only the lanes of
                // the vector which fail, iteratively reducing the chance of
                // rejection. The replacement method does however add a little
                // overhead. Benchmarking or calculating probabilities might
                // reveal contexts where this replacement method is slower.
                let mut v: $unsigned = rng.gen();
                loop {
                    let (hi, lo) = v.wmul(range);
                    let mask = lo.le(zone);
                    if mask.all() {
                        let hi: $ty = hi.cast();
                        // wrapping addition
                        let result = self.low + hi;
                        // `select` here compiles to a blend operation
                        // When `range.eq(0).none()` the compare and blend
                        // operations are avoided.
                        let v: $ty = v.cast();
                        return range.gt($unsigned::splat(0)).select(result, v);
                    }
                    // Replace only the failing lanes
                    v = mask.select(v, rng.gen());
                }
            }
        }
    };

    // bulk implementation
    ($(($unsigned:ident, $signed:ident),)+ $u_scalar:ident) => {
        $(
            uniform_simd_int_impl!($unsigned, $unsigned, $u_scalar);
            uniform_simd_int_impl!($signed, $unsigned, $u_scalar);
        )+
    };
}

uniform_simd_int_impl! {
    (u64x2, i64x2),
    (u64x4, i64x4),
    (u64x8, i64x8),
    u64
}

uniform_simd_int_impl! {
    (u32x2, i32x2),
    (u32x4, i32x4),
    (u32x8, i32x8),
    (u32x16, i32x16),
    u32
}

uniform_simd_int_impl! {
    (u16x2, i16x2),
    (u16x4, i16x4),
    (u16x8, i16x8),
    (u16x16, i16x16),
    (u16x32, i16x32),
    u16
}

uniform_simd_int_impl! {
    (u8x2, i8x2),
    (u8x4, i8x4),
    (u8x8, i8x8),
    (u8x16, i8x16),
    (u8x32, i8x32),
    (u8x64, i8x64),
    u8
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::distributions::uniform::Uniform;

    #[test]
    #[cfg_attr(miri, ignore)] // Miri is too slow
    fn test_integers() {
        use core::{i16, i32, i64, i8};
        use core::{u16, u32, u64, u8};

        let mut rng = crate::test::rng(251);
        macro_rules! t {
            ($ty:ident, $v:expr, $le:expr, $lt:expr) => {{
                for &(low, high) in $v.iter() {
                    let my_uniform = Uniform::new(low, high);
                    for _ in 0..1000 {
                        let v: $ty = rng.sample(my_uniform);
                        assert!($le(low, v) && $lt(v, high));
                    }

                    let my_uniform = Uniform::new_inclusive(low, high);
                    for _ in 0..1000 {
                        let v: $ty = rng.sample(my_uniform);
                        assert!($le(low, v) && $le(v, high));
                    }

                    let my_uniform = Uniform::new(&low, high);
                    for _ in 0..1000 {
                        let v: $ty = rng.sample(my_uniform);
                        assert!($le(low, v) && $lt(v, high));
                    }

                    let my_uniform = Uniform::new_inclusive(&low, &high);
                    for _ in 0..1000 {
                        let v: $ty = rng.sample(my_uniform);
                        assert!($le(low, v) && $le(v, high));
                    }

                    for _ in 0..1000 {
                        let v = <$ty as SampleUniform>::Sampler::sample_single(low, high, &mut rng);
                        assert!($le(low, v) && $lt(v, high));
                    }

                    for _ in 0..1000 {
                        let v = <$ty as SampleUniform>::Sampler::sample_single_inclusive(low, high, &mut rng);
                        assert!($le(low, v) && $le(v, high));
                    }
                }
            }};

            // simd bulk
            ($($ty:ident),* => $scalar:ident) => {{
                $(t!(
                    $ty,
                    [
                        ($ty::splat(0), $ty::splat(10)),
                        ($ty::splat(10), $ty::splat(127)),
                        ($ty::splat($scalar::MIN), $ty::splat($scalar::MAX)),
                    ],
                    |x: $ty, y| x.le(y).all(),
                    |x: $ty, y| x.lt(y).all()
                );)*
            }};
        }

        t!(u8x2, u8x4, u8x8, u8x16, u8x32, u8x64 => u8);
        t!(i8x2, i8x4, i8x8, i8x16, i8x32, i8x64 => i8);
        t!(u16x2, u16x4, u16x8, u16x16, u16x32 => u16);
        t!(i16x2, i16x4, i16x8, i16x16, i16x32 => i16);
        t!(u32x2, u32x4, u32x8, u32x16 => u32);
        t!(i32x2, i32x4, i32x8, i32x16 => i32);
        t!(u64x2, u64x4, u64x8 => u64);
        t!(i64x2, i64x4, i64x8 => i64);
    }
}
