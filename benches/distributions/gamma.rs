use std::mem::size_of;
use test::Bencher;
use rand;
use rand::distributions::Distribution;
use rand::distributions::gamma::Gamma;

#[bench]
fn bench_gamma_large_shape(b: &mut Bencher) {
    let gamma = Gamma::new(10., 1.0);
    let mut rng = rand::weak_rng();

    b.iter(|| {
        for _ in 0..::RAND_BENCH_N {
            gamma.sample(&mut rng);
        }
    });
    b.bytes = size_of::<f64>() as u64 * ::RAND_BENCH_N;
}

#[bench]
fn bench_gamma_small_shape(b: &mut Bencher) {
    let gamma = Gamma::new(0.1, 1.0);
    let mut rng = rand::weak_rng();

    b.iter(|| {
        for _ in 0..::RAND_BENCH_N {
            gamma.sample(&mut rng);
        }
    });
    b.bytes = size_of::<f64>() as u64 * ::RAND_BENCH_N;
}
