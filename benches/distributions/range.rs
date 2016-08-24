use std::mem::size_of;
use std::cmp;
use test::Bencher;
use rand;
use rand::distributions::Sample;
use rand::distributions::Range;

#[bench]
fn rand_range(b: &mut Bencher) {
    let mut rng = rand::weak_rng();
    let mut range = Range::new(10, 10000);
    b.iter(|| {
        for _ in 0..::RAND_BENCH_N {
            range.sample(&mut rng);
        }
    });
    b.bytes = size_of::<u32>() as u64 * ::RAND_BENCH_N;
}
