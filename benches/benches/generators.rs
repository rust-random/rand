// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use chacha20::rand_core::UnwrapErr;
use chacha20::{ChaCha8Rng, ChaCha12Rng, ChaCha20Core, ChaCha20Rng};
use core::time::Duration;
use criterion::measurement::WallTime;
use criterion::{BenchmarkGroup, Criterion, black_box, criterion_group, criterion_main};
use rand::prelude::*;
use rand::rngs::OsRng;
use rand::rngs::ReseedingRng;
use rand_pcg::{Pcg32, Pcg64, Pcg64Dxsm, Pcg64Mcg};

criterion_group!(
    name = benches;
    config = Criterion::default();
    targets = random_bytes, random_u32, random_u64, init_gen, init_from_u64, init_from_seed, reseeding_bytes
);
criterion_main!(benches);

pub fn random_bytes(c: &mut Criterion) {
    let mut g = c.benchmark_group("random_bytes");
    g.warm_up_time(Duration::from_millis(500));
    g.measurement_time(Duration::from_millis(1000));
    g.throughput(criterion::Throughput::Bytes(1024));

    fn bench(g: &mut BenchmarkGroup<WallTime>, name: &str, mut rng: impl Rng) {
        g.bench_function(name, |b| {
            let mut buf = [0u8; 1024];
            b.iter(|| {
                rng.fill_bytes(&mut buf);
                black_box(buf);
            });
        });
    }

    bench(&mut g, "pcg32", Pcg32::from_rng(&mut rand::rng()));
    bench(&mut g, "pcg64", Pcg64::from_rng(&mut rand::rng()));
    bench(&mut g, "pcg64mcg", Pcg64Mcg::from_rng(&mut rand::rng()));
    bench(&mut g, "pcg64dxsm", Pcg64Dxsm::from_rng(&mut rand::rng()));
    bench(&mut g, "chacha8", ChaCha8Rng::from_rng(&mut rand::rng()));
    bench(&mut g, "chacha12", ChaCha12Rng::from_rng(&mut rand::rng()));
    bench(&mut g, "chacha20", ChaCha20Rng::from_rng(&mut rand::rng()));
    bench(&mut g, "std", StdRng::from_rng(&mut rand::rng()));
    bench(&mut g, "small", SmallRng::from_rng(&mut rand::rng()));
    bench(&mut g, "os", UnwrapErr(OsRng));
    bench(&mut g, "thread", rand::rng());

    g.finish()
}

pub fn random_u32(c: &mut Criterion) {
    let mut g = c.benchmark_group("random_u32");
    g.sample_size(1000);
    g.warm_up_time(Duration::from_millis(500));
    g.measurement_time(Duration::from_millis(1000));
    g.throughput(criterion::Throughput::Bytes(4));

    fn bench(g: &mut BenchmarkGroup<WallTime>, name: &str, mut rng: impl Rng) {
        g.bench_function(name, |b| {
            b.iter(|| rng.random::<u32>());
        });
    }

    bench(&mut g, "pcg32", Pcg32::from_rng(&mut rand::rng()));
    bench(&mut g, "pcg64", Pcg64::from_rng(&mut rand::rng()));
    bench(&mut g, "pcg64mcg", Pcg64Mcg::from_rng(&mut rand::rng()));
    bench(&mut g, "pcg64dxsm", Pcg64Dxsm::from_rng(&mut rand::rng()));
    bench(&mut g, "chacha8", ChaCha8Rng::from_rng(&mut rand::rng()));
    bench(&mut g, "chacha12", ChaCha12Rng::from_rng(&mut rand::rng()));
    bench(&mut g, "chacha20", ChaCha20Rng::from_rng(&mut rand::rng()));
    bench(&mut g, "std", StdRng::from_rng(&mut rand::rng()));
    bench(&mut g, "small", SmallRng::from_rng(&mut rand::rng()));
    bench(&mut g, "os", UnwrapErr(OsRng));
    bench(&mut g, "thread", rand::rng());

    g.finish()
}

pub fn random_u64(c: &mut Criterion) {
    let mut g = c.benchmark_group("random_u64");
    g.sample_size(1000);
    g.warm_up_time(Duration::from_millis(500));
    g.measurement_time(Duration::from_millis(1000));
    g.throughput(criterion::Throughput::Bytes(8));

    fn bench(g: &mut BenchmarkGroup<WallTime>, name: &str, mut rng: impl Rng) {
        g.bench_function(name, |b| {
            b.iter(|| rng.random::<u64>());
        });
    }

    bench(&mut g, "pcg32", Pcg32::from_rng(&mut rand::rng()));
    bench(&mut g, "pcg64", Pcg64::from_rng(&mut rand::rng()));
    bench(&mut g, "pcg64mcg", Pcg64Mcg::from_rng(&mut rand::rng()));
    bench(&mut g, "pcg64dxsm", Pcg64Dxsm::from_rng(&mut rand::rng()));
    bench(&mut g, "chacha8", ChaCha8Rng::from_rng(&mut rand::rng()));
    bench(&mut g, "chacha12", ChaCha12Rng::from_rng(&mut rand::rng()));
    bench(&mut g, "chacha20", ChaCha20Rng::from_rng(&mut rand::rng()));
    bench(&mut g, "std", StdRng::from_rng(&mut rand::rng()));
    bench(&mut g, "small", SmallRng::from_rng(&mut rand::rng()));
    bench(&mut g, "os", UnwrapErr(OsRng));
    bench(&mut g, "thread", rand::rng());

    g.finish()
}

pub fn init_gen(c: &mut Criterion) {
    let mut g = c.benchmark_group("init_gen");
    g.warm_up_time(Duration::from_millis(500));
    g.measurement_time(Duration::from_millis(1000));

    fn bench<R: SeedableRng>(g: &mut BenchmarkGroup<WallTime>, name: &str) {
        g.bench_function(name, |b| {
            let mut rng = Pcg32::from_rng(&mut rand::rng());
            b.iter(|| R::from_rng(&mut rng));
        });
    }

    bench::<Pcg32>(&mut g, "pcg32");
    bench::<Pcg64>(&mut g, "pcg64");
    bench::<Pcg64Mcg>(&mut g, "pcg64mcg");
    bench::<Pcg64Dxsm>(&mut g, "pcg64dxsm");
    bench::<ChaCha8Rng>(&mut g, "chacha8");
    bench::<ChaCha12Rng>(&mut g, "chacha12");
    bench::<ChaCha20Rng>(&mut g, "chacha20");
    bench::<StdRng>(&mut g, "std");
    bench::<SmallRng>(&mut g, "small");

    g.finish()
}

pub fn init_from_u64(c: &mut Criterion) {
    let mut g = c.benchmark_group("init_from_u64");
    g.warm_up_time(Duration::from_millis(500));
    g.measurement_time(Duration::from_millis(1000));

    fn bench<R: SeedableRng>(g: &mut BenchmarkGroup<WallTime>, name: &str) {
        g.bench_function(name, |b| {
            let mut rng = Pcg32::from_rng(&mut rand::rng());
            let seed = rng.random();
            b.iter(|| R::seed_from_u64(black_box(seed)));
        });
    }

    bench::<Pcg32>(&mut g, "pcg32");
    bench::<Pcg64>(&mut g, "pcg64");
    bench::<Pcg64Mcg>(&mut g, "pcg64mcg");
    bench::<Pcg64Dxsm>(&mut g, "pcg64dxsm");
    bench::<ChaCha8Rng>(&mut g, "chacha8");
    bench::<ChaCha12Rng>(&mut g, "chacha12");
    bench::<ChaCha20Rng>(&mut g, "chacha20");
    bench::<StdRng>(&mut g, "std");
    bench::<SmallRng>(&mut g, "small");

    g.finish()
}

pub fn init_from_seed(c: &mut Criterion) {
    let mut g = c.benchmark_group("init_from_seed");
    g.warm_up_time(Duration::from_millis(500));
    g.measurement_time(Duration::from_millis(1000));

    fn bench<R: SeedableRng>(g: &mut BenchmarkGroup<WallTime>, name: &str)
    where
        rand::distr::StandardUniform: Distribution<<R as SeedableRng>::Seed>,
    {
        g.bench_function(name, |b| {
            let mut rng = Pcg32::from_rng(&mut rand::rng());
            let seed = rng.random();
            b.iter(|| R::from_seed(black_box(seed.clone())));
        });
    }

    bench::<Pcg32>(&mut g, "pcg32");
    bench::<Pcg64>(&mut g, "pcg64");
    bench::<Pcg64Mcg>(&mut g, "pcg64mcg");
    bench::<Pcg64Dxsm>(&mut g, "pcg64dxsm");
    bench::<ChaCha8Rng>(&mut g, "chacha8");
    bench::<ChaCha12Rng>(&mut g, "chacha12");
    bench::<ChaCha20Rng>(&mut g, "chacha20");
    bench::<StdRng>(&mut g, "std");
    bench::<SmallRng>(&mut g, "small");

    g.finish()
}

pub fn reseeding_bytes(c: &mut Criterion) {
    let mut g = c.benchmark_group("reseeding_bytes");
    g.warm_up_time(Duration::from_millis(500));
    g.throughput(criterion::Throughput::Bytes(1024 * 1024));

    fn bench(g: &mut BenchmarkGroup<WallTime>, thresh: u64) {
        let name = format!("chacha20_{thresh}k");
        g.bench_function(name.as_str(), |b| {
            let mut rng = ReseedingRng::<ChaCha20Core, _>::new(thresh * 1024, OsRng).unwrap();
            let mut buf = [0u8; 1024 * 1024];
            b.iter(|| {
                rng.fill_bytes(&mut buf);
                black_box(&buf);
            });
        });
    }

    bench(&mut g, 4);
    bench(&mut g, 16);
    bench(&mut g, 32);
    bench(&mut g, 64);
    bench(&mut g, 256);
    bench(&mut g, 1024);

    g.finish()
}
