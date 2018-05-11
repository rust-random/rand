#![cfg(feature = "std")]

extern crate rand;
extern crate libc;

use rand::rngs::SmallRng;
use rand::FromEntropy;
use rand::distributions::{Distribution, Bernoulli};

#[link_name = "m"]
extern "C" {
    fn nextafter(x: f64, y: f64) -> f64;
}

/// This test should make sure that we don't accidentally have undefined
/// behavior for large propabilties due to
/// https://github.com/rust-lang/rust/issues/10184.
#[test]
fn large_probability() {
    let p = unsafe { nextafter(1., 0.) };
    assert!(p < 1.);
    let d = Bernoulli::new(p);
    let mut rng = SmallRng::from_entropy();
    for _ in 0..10 {
        assert!(d.sample(&mut rng));
    }
}
