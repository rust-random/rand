// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
//! The Bernoulli distribution.

use Rng;
use distributions::Distribution;

/// The Bernoulli distribution.
///
/// This is a special case of the Binomial distribution where `n = 1`.
///
/// # Example
///
/// ```rust
/// use rand::distributions::{Bernoulli, Distribution};
///
/// let d = Bernoulli::new(0.3);
/// let v = d.sample(&mut rand::thread_rng());
/// println!("{} is from a Bernoulli distribution", v);
/// ```
///
/// # Precision
///
/// This `Bernoulli` distribution uses 64 bits from the RNG (a `u64`),
/// so only probabilities that are multiples of 2<sup>-64</sup> can be
/// represented.
#[derive(Clone, Copy, Debug)]
pub struct Bernoulli {
    /// Probability of success, relative to the maximal integer.
    p_int: u64,
}

impl Bernoulli {
    /// Construct a new `Bernoulli` with the given probability of success `p`.
    ///
    /// # Panics
    ///
    /// If `p < 0` or `p > 1`.
    ///
    /// # Precision
    ///
    /// For `p = 1.0`, the resulting distribution will always generate true.
    /// For `p = 0.0`, the resulting distribution will always generate false.
    ///
    /// This method is accurate for any input `p` in the range `[0, 1]` which is
    /// a multiple of 2<sup>-64</sup>. (Note that not all multiples of
    /// 2<sup>-64</sup> in `[0, 1]` can be represented as a `f64`.)
    #[inline]
    pub fn new(p: f64) -> Bernoulli {
        assert!((p >= 0.0) & (p <= 1.0), "Bernoulli::new not called with 0 <= p <= 0");
        // Technically, this should be 2^64 or `u64::MAX + 1` because we compare
        // using `<` when sampling. However, `u64::MAX` rounds to an `f64`
        // larger than `u64::MAX` anyway.
        const MAX_P_INT: f64 = ::core::u64::MAX as f64;
        let p_int = if p < 1.0 {
            (p * MAX_P_INT) as u64
        } else {
            // Avoid overflow: `MAX_P_INT` cannot be represented as u64.
            ::core::u64::MAX
        };
        Bernoulli { p_int }
    }
}

impl Distribution<bool> for Bernoulli {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> bool {
        // Make sure to always return true for p = 1.0.
        if self.p_int == ::core::u64::MAX {
            return true;
        }
        let r: u64 = rng.gen();
        r < self.p_int
    }
}

#[cfg(test)]
mod test {
    use Rng;
    use distributions::Distribution;
    use super::Bernoulli;

    #[test]
    fn test_trivial() {
        let mut r = ::test::rng(1);
        let always_false = Bernoulli::new(0.0);
        let always_true = Bernoulli::new(1.0);
        for _ in 0..5 {
            assert_eq!(r.sample::<bool, _>(&always_false), false);
            assert_eq!(r.sample::<bool, _>(&always_true), true);
            assert_eq!(Distribution::<bool>::sample(&always_false, &mut r), false);
            assert_eq!(Distribution::<bool>::sample(&always_true, &mut r), true);
        }
    }

    #[test]
    fn test_average() {
        const P: f64 = 0.3;
        let d = Bernoulli::new(P);
        const N: u32 = 10_000_000;

        let mut sum: u32 = 0;
        let mut rng = ::test::rng(2);
        for _ in 0..N {
            if d.sample(&mut rng) {
                sum += 1;
            }
        }
        let avg = (sum as f64) / (N as f64);

        assert!((avg - P).abs() < 1e-3);
    }
}
