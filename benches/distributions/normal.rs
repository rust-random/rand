use std::mem::size_of;
use test::Bencher;
use rand;
use rand::distributions::Distribution;
use rand::distributions::normal::{Normal, LogNormal};

#[bench]
fn rand_normal(b: &mut Bencher) {
    let mut rng = rand::weak_rng();
    let normal = Normal::new(-2.71828, 3.14159);

    b.iter(|| {
        for _ in 0..::RAND_BENCH_N {
            normal.sample(&mut rng);
        }
    });
    b.bytes = size_of::<f64>() as u64 * ::RAND_BENCH_N;
}

#[bench]
fn rand_log_normal(b: &mut Bencher) {
    let mut rng = rand::weak_rng();
    let log_normal = LogNormal::new(-2.71828, 3.14159);

    b.iter(|| {
        for _ in 0..::RAND_BENCH_N {
            log_normal.sample(&mut rng);
        }
    });
    b.bytes = size_of::<f64>() as u64 * ::RAND_BENCH_N;
}
