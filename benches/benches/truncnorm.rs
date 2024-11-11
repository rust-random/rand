use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use criterion_cycles_per_byte::CyclesPerByte;

use rand::prelude::*;
use rand_distr::*;

// At this time, distributions are optimised for 64-bit platforms.
use rand_pcg::Pcg64Mcg;

struct TruncatedNormalByRejection {
    normal: Normal<f64>,
    a: f64,
    b: f64,
}

impl TruncatedNormalByRejection {
    fn new(mean: f64, std_dev: f64, a: f64, b: f64) -> Self {
        Self {
            normal: Normal::new(mean, std_dev).unwrap(),
            a,
            b,
        }
    }
}

impl Distribution<f64> for TruncatedNormalByRejection {
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> f64 {
        let mut value;
        loop {
            value = rng.sample(self.normal);
            if value >= self.a && value <= self.b {
                return value;
            }
        }
    }
}

fn bench(c: &mut Criterion<CyclesPerByte>) {
    let distr = TruncatedNormal::new(0., 1., f64::NEG_INFINITY, f64::INFINITY).unwrap();

    let ranges = [
        (1, f64::NEG_INFINITY, distr.ppf(0.01)),
        (3, f64::NEG_INFINITY, distr.ppf(0.03)),
        (5, f64::NEG_INFINITY, distr.ppf(0.05)),
        (7, f64::NEG_INFINITY, distr.ppf(0.07)),
        (10, f64::NEG_INFINITY, distr.ppf(0.1)),
        (30, f64::NEG_INFINITY, distr.ppf(0.3)),
        (50, f64::NEG_INFINITY, distr.ppf(0.5)),
        (70, f64::NEG_INFINITY, distr.ppf(0.7)),
        (100, f64::NEG_INFINITY, f64::INFINITY),
    ];

    let mut g = c.benchmark_group("truncnorm by rejection");
    for range in &ranges {
        let mut rng = Pcg64Mcg::from_os_rng();
        g.throughput(Throughput::Elements(range.0));
        g.bench_with_input(BenchmarkId::from_parameter(range.0), range, |b, &range| {
            let distr = TruncatedNormalByRejection::new(0.0, 1.0, range.1, range.2);
            b.iter(|| std::hint::black_box(Distribution::<f64>::sample(&distr, &mut rng)));
        });
    }
    g.finish();

    let mut g = c.benchmark_group("truncnorm by ppf");
    for range in &ranges {
        let mut rng = Pcg64Mcg::from_os_rng();
        g.throughput(Throughput::Elements(range.0));
        g.bench_with_input(BenchmarkId::from_parameter(range.0), range, |b, &range| {
            let distr = TruncatedNormal::new(0.0, 1.0, range.1, range.2).unwrap();
            b.iter(|| std::hint::black_box(Distribution::<f64>::sample(&distr, &mut rng)));
        });
    }
    g.finish();
}

criterion_group!(
    name = benches;
    config = Criterion::default().with_measurement(CyclesPerByte)
        .warm_up_time(core::time::Duration::from_secs(1))
        .measurement_time(core::time::Duration::from_secs(2));
    targets = bench
);
criterion_main!(benches);
