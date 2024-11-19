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
use rand::seq::{IndexedRandom, IteratorRandom};
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

#[test]
fn choose_one_weighted_indexed() {
    struct Adapter<F: Fn(i64) -> f64>(Vec<i64>, F);
    impl<F: Fn(i64) -> f64> Distribution<i64> for Adapter<F> {
        fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> i64 {
            *IndexedRandom::choose_multiple_weighted(&self.0[..], rng, 1, |i| (self.1)(*i))
                .unwrap()
                .next()
                .unwrap()
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

#[test]
fn choose_two_weighted_indexed() {
    struct Adapter<F: Fn(i64) -> f64>(Vec<i64>, F);
    impl<F: Fn(i64) -> f64> Distribution<i64> for Adapter<F> {
        fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> i64 {
            let mut iter =
                IndexedRandom::choose_multiple_weighted(&self.0[..], rng, 2, |i| (self.1)(*i))
                    .unwrap();
            let mut a = *iter.next().unwrap();
            let mut b = *iter.next().unwrap();
            assert!(iter.next().is_none());
            if b < a {
                std::mem::swap(&mut a, &mut b);
            }
            a * self.0.len() as i64 + b
        }
    }

    fn test_weights(num: usize, weight: impl Fn(i64) -> f64) {
        let distr = Adapter((0..num).map(|i| i as i64).collect(), &weight);

        let pmf1 = (0..num).map(|i| weight(i as i64)).collect::<Vec<f64>>();
        let sum: f64 = pmf1.iter().sum();
        let frac = 1.0 / sum;

        let mut ac = 0.0;
        let mut cdf = Vec::with_capacity(num * num);
        for a in 0..num {
            for b in 0..num {
                if a < b {
                    let pa = pmf1[a] * frac;
                    let pab = pa * pmf1[b] / (sum - pmf1[a]);

                    let pb = pmf1[b] * frac;
                    let pba = pb * pmf1[a] / (sum - pmf1[b]);

                    ac += pab + pba;
                }
                cdf.push(ac);
            }
        }
        assert!((cdf.last().unwrap() - 1.0).abs() < 1e-9);

        let cdf = |i| {
            if i < 0 {
                0.0
            } else {
                cdf[i as usize]
            }
        };

        test_discrete(0, distr, cdf);
    }

    test_weights(100, |_| 1.0);
    test_weights(100, |i| ((i + 1) as f64).ln());
    test_weights(100, |i| i as f64);
    test_weights(100, |i| (i as f64).powi(3));
    test_weights(100, |i| 1.0 / ((i + 1) as f64));
    test_weights(10, |i| ((i + 1) as f64).powi(-8));
}

#[test]
fn choose_iterator() {
    struct Adapter<I>(I);
    impl<I: Clone + Iterator<Item = i64>> Distribution<i64> for Adapter<I> {
        fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> i64 {
            IteratorRandom::choose(self.0.clone(), rng).unwrap()
        }
    }

    let distr = Adapter((0..100).map(|i| i as i64));
    test_discrete(0, distr, make_cdf(100, |_| 1.0));
}

#[test]
fn choose_stable_iterator() {
    struct Adapter<I>(I);
    impl<I: Clone + Iterator<Item = i64>> Distribution<i64> for Adapter<I> {
        fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> i64 {
            IteratorRandom::choose_stable(self.0.clone(), rng).unwrap()
        }
    }

    let distr = Adapter((0..100).map(|i| i as i64));
    test_discrete(0, distr, make_cdf(100, |_| 1.0));
}

#[test]
fn choose_two_iterator() {
    struct Adapter<I>(I);
    impl<I: Clone + Iterator<Item = i64>> Distribution<i64> for Adapter<I> {
        fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> i64 {
            let mut buf = [0; 2];
            IteratorRandom::choose_multiple_fill(self.0.clone(), rng, &mut buf);
            buf.sort_unstable();
            assert!(buf[0] < 99 && buf[1] >= 1);
            let a = buf[0];
            4950 - (99 - a) * (100 - a) / 2 + buf[1] - a - 1
        }
    }

    let distr = Adapter((0..100).map(|i| i as i64));

    test_discrete(
        0,
        distr,
        |i| if i < 0 { 0.0 } else { (i + 1) as f64 / 4950.0 },
    );
}
