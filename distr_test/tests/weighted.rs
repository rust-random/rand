// Copyright 2024 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

mod ks;
use ks::test_discrete;
use rand::distr::WeightedIndex;

#[test]
fn weighted_index() {
    fn test_weights(num: usize, weight: impl Fn(i64) -> f64) {
        let distr = WeightedIndex::new((0..num).map(|i| weight(i as i64))).unwrap();

        let mut cdf = Vec::with_capacity(num);
        let mut ac = 0.0;
        for i in 0..num {
            ac += weight(i as i64);
            cdf.push(ac);
        }
        let frac = 1.0 / ac;
        for x in &mut cdf {
            *x = *x * frac;
        }

        test_discrete(0, distr, |i| if i < 0 { 0.0 } else { cdf[i as usize] });
    }

    test_weights(100, |_| 1.0);
    test_weights(100, |i| ((i + 1) as f64).ln());
    test_weights(100, |i| i as f64);
    test_weights(100, |i| (i as f64).powi(3));
    test_weights(100, |i| 1.0 / ((i + 1) as f64));
}
