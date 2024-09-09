// Copyright 2019 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use core::time::Duration;
use criterion::measurement::WallTime;
use criterion::{criterion_group, criterion_main, BenchmarkGroup, Criterion};
use rand::distr::{Alphanumeric, Standard};
use rand::prelude::*;
use rand_distr::{Open01, OpenClosed01};
use rand_pcg::Pcg64Mcg;

criterion_group!(
    name = benches;
    config = Criterion::default();
    targets = bench
);
criterion_main!(benches);

fn bench_ty<T, D>(g: &mut BenchmarkGroup<WallTime>, name: &str)
where
    D: Distribution<T> + Default,
{
    g.throughput(criterion::Throughput::Bytes(size_of::<T>() as u64));
    g.bench_function(name, |b| {
        let mut rng = Pcg64Mcg::from_os_rng();

        b.iter(|| rng.sample::<T, _>(D::default()));
    });
}

pub fn bench(c: &mut Criterion) {
    let mut g = c.benchmark_group("Standard");
    g.sample_size(1000);
    g.warm_up_time(Duration::from_millis(500));
    g.measurement_time(Duration::from_millis(1000));

    macro_rules! do_ty {
        ($t:ty) => {
            bench_ty::<$t, Standard>(&mut g, stringify!($t));
        };
        ($t:ty, $($tt:ty),*) => {
            do_ty!($t);
            do_ty!($($tt),*);
        };
    }

    do_ty!(i8, i16, i32, i64, i128);
    do_ty!(f32, f64);
    do_ty!(char);

    bench_ty::<u8, Alphanumeric>(&mut g, "Alphanumeric");

    bench_ty::<f32, Open01>(&mut g, "Open01/f32");
    bench_ty::<f64, Open01>(&mut g, "Open01/f64");
    bench_ty::<f32, OpenClosed01>(&mut g, "OpenClosed01/f32");
    bench_ty::<f64, OpenClosed01>(&mut g, "OpenClosed01/f64");

    g.finish();
}
