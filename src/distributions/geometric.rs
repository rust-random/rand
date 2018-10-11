// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The Geometric distribution.

use Rng;
use distributions::Distribution;

use std::f64;

/// The Geometric distribution.
///
/// This distribution is the number of failures in Bernoulli trials
/// before one success.
///
/// # Example
///
/// ```rust
/// use rand::distributions::{Geometric, Distribution};
///
/// let d = Geometric::new(0.3);
/// let v = d.sample(&mut rand::thread_rng());
/// println!("{} is from a Geometric distribution", v);
/// ```
///
#[derive(Clone, Copy, Debug)]
pub struct Geometric {
    /// Probability of success
    prob: f64,
}

// To sample from the Geometric distribution we simply sample from a uniform
// distribution and apply "floor (log(q) / log(1 - p))".
//
// If `p == 1.0`, simply return 0, as we will always succeed on the first trial.
//

impl Geometric {
    /// Construct a new `Geometric` with the given probability of success `p`.
    ///
    /// For `p = 1.0`, the resulting distribution will always generate 0.
    ///
    /// # Panics
    ///
    /// If `p <= 0` or `p > 1`.
    ///
    #[inline]
    pub fn new(p: f64) -> Geometric {
        if p <= 0.0 || p > 1.0 {
            panic!("Geometric::new not called with 0.0 < p <= 1.0");
        }
        Geometric { prob: p }
    }
}

impl Distribution<u64> for Geometric {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u64 {
        // Make sure to always return 0 for p = 1.0.
        if self.prob == 1.0 { return 0; }
        let q: f64 = rng.gen();
        (q.ln() / (1.0 - self.prob).ln()).floor() as u64
    }
}

#[cfg(test)]
mod test {
    use Rng;
    use distributions::Distribution;
    use super::Geometric;

    #[test]
    fn test_trivial() {
        let mut r = ::test::rng(1);
        let always_succeed = Geometric::new(1.0);
        for _ in 0..5 {
            assert_eq!(r.sample::<u64, _>(&always_succeed), 0);
            assert_eq!(Distribution::<u64>::sample(&always_succeed, &mut r), 0);
        }
    }

    #[test]
    fn test_average() {
        const P: f64 = 0.3;
        const EXPECTED_AVG : f64 = (1.0 / P) as f64;
        let geo = Geometric::new(P);
        const N: u32 = 100_000;

        let mut sum: u64 = 0;
        let mut rng = ::test::rng(2);
        for _ in 0..N {
            sum += geo.sample(&mut rng);
        }
        let avg = (sum as f64) / (N as f64);
        assert!((avg.abs() - EXPECTED_AVG) < 5e-3);
    }
}
