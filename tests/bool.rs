#![no_std]

extern crate rand;

use rand::SeedableRng;
use rand::rngs::SmallRng;
use rand::distributions::{Distribution, Bernoulli};

/// This test should make sure that we don't accidentally have undefined
/// behavior for large propabilties due to
/// https://github.com/rust-lang/rust/issues/10184.
/// Expressions like `1.0*(u64::MAX as f64) as u64` have to be avoided.
#[test]
fn large_probability() {
    let p = 1. - ::core::f64::EPSILON / 2.;
    assert!(p < 1.);
    let d = Bernoulli::new(p);
    let mut rng = SmallRng::from_seed(
        [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]);
    for _ in 0..10 {
        assert!(d.sample(&mut rng), "extremely unlikely to fail by accident");
    }
}
