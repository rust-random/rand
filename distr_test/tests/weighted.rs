// Copyright 2024 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

mod ks;
use ks::test_discrete;
use rand::distr::{Distribution, WeightedIndex};
use rand::seq::IndexedRandom;
use rand_distr::{WeightedAliasIndex, WeightedTreeIndex};

fn make_cdf(num: usize, f: impl Fn(i64) -> f64) -> impl Fn(i64) -> f64 {
    let mut cdf = Vec::with_capacity(num);
    let mut ac = 0.0;
    for i in 0..num {
        ac += f(i as i64);
        cdf.push(ac);
    }

    let frac = 1.0 / ac;
    for x in &mut cdf {
        *x = *x * frac;
    }

    move |i| {
        if i < 0 {
            0.0
        } else {
            cdf[i as usize]
        }
    }
}

#[test]
fn weighted_index() {
    fn test_weights(num: usize, weight: impl Fn(i64) -> f64) {
        let distr = WeightedIndex::new((0..num).map(|i| weight(i as i64))).unwrap();
        test_discrete(0, distr, make_cdf(num, weight));
    }

    test_weights(100, |_| 1.0);
    test_weights(100, |i| ((i + 1) as f64).ln());
    test_weights(100, |i| i as f64);
    test_weights(100, |i| (i as f64).powi(3));
    test_weights(100, |i| 1.0 / ((i + 1) as f64));
}

#[test]
fn weighted_alias_index() {
    fn test_weights(num: usize, weight: impl Fn(i64) -> f64) {
        let weights = (0..num).map(|i| weight(i as i64)).collect();
        let distr = WeightedAliasIndex::new(weights).unwrap();
        test_discrete(0, distr, make_cdf(num, weight));
    }

    test_weights(100, |_| 1.0);
    test_weights(100, |i| ((i + 1) as f64).ln());
    test_weights(100, |i| i as f64);
    test_weights(100, |i| (i as f64).powi(3));
    test_weights(100, |i| 1.0 / ((i + 1) as f64));
}

#[test]
fn weighted_tree_index() {
    fn test_weights(num: usize, weight: impl Fn(i64) -> f64) {
        let distr = WeightedTreeIndex::new((0..num).map(|i| weight(i as i64))).unwrap();
        test_discrete(0, distr, make_cdf(num, weight));
    }

    test_weights(100, |_| 1.0);
    test_weights(100, |i| ((i + 1) as f64).ln());
    test_weights(100, |i| i as f64);
    test_weights(100, |i| (i as f64).powi(3));
    test_weights(100, |i| 1.0 / ((i + 1) as f64));
}

#[test]
fn choose_weighted_indexed() {
    struct Adapter<F: Fn(i64) -> f64>(Vec<i64>, F);
    impl<F: Fn(i64) -> f64> Distribution<i64> for Adapter<F> {
        fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> i64 {
            *IndexedRandom::choose_weighted(&self.0[..], rng, |i| (self.1)(*i)).unwrap()
        }
    }

    fn test_weights(num: usize, weight: impl Fn(i64) -> f64) {
        let distr = Adapter((0..num).map(|i| i as i64).collect(), &weight);
        test_discrete(0, distr, make_cdf(num, |i| weight(i)));
    }

    test_weights(100, |_| 1.0);
    test_weights(100, |i| ((i + 1) as f64).ln());
    test_weights(100, |i| i as f64);
    test_weights(100, |i| (i as f64).powi(3));
    test_weights(100, |i| 1.0 / ((i + 1) as f64));
}
