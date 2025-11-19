// Copyright 2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Implement benchmarks for uniform distributions over integer types

#![cfg_attr(feature = "simd_support", feature(portable_simd))]

use chacha20::ChaCha8Rng;
use core::time::Duration;
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use rand::distr::uniform::{SampleRange, Uniform};
use rand::prelude::*;
use rand_pcg::{Pcg32, Pcg64};
#[cfg(feature = "simd_support")]
use std::simd::{Simd, num::SimdUint};

const WARM_UP_TIME: Duration = Duration::from_millis(1000);
const MEASUREMENT_TIME: Duration = Duration::from_secs(3);
const SAMPLE_SIZE: usize = 100_000;
const N_RESAMPLES: usize = 10_000;

macro_rules! sample {
    (@range $T:ty, $U:ty, 1, $rng:ident) => {{
        assert_eq!(<$T>::BITS, <$U>::BITS);
        let bits = (<$T>::BITS / 2);
        let mask = (1 as $U).wrapping_neg() >> bits;
        let x = $rng.random::<$U>();
        ((x >> bits) * (x & mask)) as $T
    }};

    (@range $T:ty, $U:ty, $len:tt, $rng:ident) => {{
        let bits = (<$T>::BITS / 2);
        let mask = Simd::splat((1 as $U).wrapping_neg() >> bits);
        let bits = Simd::splat(bits as $U);
        let x = $rng.random::<Simd<$U, $len>>();
        ((x >> bits) * (x & mask)).cast()
    }};

    (@MIN $T:ty, 1) => {
        <$T>::MIN
    };

    (@MIN $T:ty, $len:tt) => {
        Simd::<$T, $len>::splat(<$T>::MIN)
    };

    (@wrapping_add $lhs:expr, $rhs:expr, 1) => {
        $lhs.wrapping_add($rhs)
    };

    (@wrapping_add $lhs:expr, $rhs:expr, $len:tt) => {
        ($lhs + $rhs)
    };

    ($R:ty, $T:ty, $U:ty, $len:tt, $g:expr) => {
        $g.bench_function(BenchmarkId::new(stringify!($R), "single"), |b| {
            let mut rng = <$R>::from_rng(&mut rand::rng());
            let range = sample!(@range $T, $U, $len, rng);
            let low = sample!(@MIN $T, $len);
            let high = sample!(@wrapping_add low, range, $len);

            b.iter(|| (low..=high).sample_single(&mut rng));
        });

        $g.bench_function(BenchmarkId::new(stringify!($R), "distr"), |b| {
            let mut rng = <$R>::from_rng(&mut rand::rng());
            let range = sample!(@range $T, $U, $len, rng);
            let low = sample!(@MIN $T, $len);
            let high = sample!(@wrapping_add low, range, $len);
            let dist = Uniform::new_inclusive(low, high).unwrap();

            b.iter(|| dist.sample(&mut rng));
        });
    };

    // Entrypoint:
    // $T is the output type (integer)
    // $U is the unsigned version of the output type
    // $len is the width for SIMD or 1 for non-SIMD
    ($c:expr, $T:ty, $U:ty, $len:tt) => {{
        let mut g = $c.benchmark_group(concat!("sample_", stringify!($T), "x", stringify!($len)));
        g.sample_size(SAMPLE_SIZE);
        g.warm_up_time(WARM_UP_TIME);
        g.measurement_time(MEASUREMENT_TIME);
        g.nresamples(N_RESAMPLES);
        sample!(SmallRng, $T, $U, $len, g);
        sample!(ChaCha8Rng, $T, $U, $len, g);
        sample!(Pcg32, $T, $U, $len, g);
        sample!(Pcg64, $T, $U, $len, g);
        g.finish();
    }};
}

fn sample(c: &mut Criterion) {
    sample!(c, i8, u8, 1);
    sample!(c, i16, u16, 1);
    sample!(c, i32, u32, 1);
    sample!(c, i64, u64, 1);
    sample!(c, i128, u128, 1);
    #[cfg(feature = "simd_support")]
    sample!(c, u8, u8, 8);
    #[cfg(feature = "simd_support")]
    sample!(c, u8, u8, 16);
    #[cfg(feature = "simd_support")]
    sample!(c, u8, u8, 32);
    #[cfg(feature = "simd_support")]
    sample!(c, u8, u8, 64);
    #[cfg(feature = "simd_support")]
    sample!(c, i16, u16, 8);
    #[cfg(feature = "simd_support")]
    sample!(c, i16, u16, 16);
    #[cfg(feature = "simd_support")]
    sample!(c, i16, u16, 32);
}

criterion_group! {
    name = benches;
    config = Criterion::default();
    targets = sample
}
criterion_main!(benches);
