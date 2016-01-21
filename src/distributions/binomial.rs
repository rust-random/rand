// Copyright 2016-2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The binomial distribution.

use Rng;
use distributions::Distribution;
use distributions::log_gamma::log_gamma;
use std::f64::consts::PI;

/// The binomial distribution `Binomial(n, p)`.
///
/// This distribution has density function: `f(k) = n!/(k! (n-k)!) p^k (1-p)^(n-k)` for `k >= 0`.
///
/// # Example
///
/// ```rust
/// use rand::distributions::{Binomial, Distribution};
///
/// let bin = Binomial::new(20, 0.3);
/// let v = bin.sample(&mut rand::thread_rng());
/// println!("{} is from a binomial distribution", v);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Binomial {
    n: u64, // number of trials
    p: f64, // probability of success
}

impl Binomial {
    /// Construct a new `Binomial` with the given shape parameters
    /// `n`, `p`. Panics if `p <= 0` or `p >= 1`.
    pub fn new(n: u64, p: f64) -> Binomial {
        assert!(p > 0.0, "Binomial::new called with `p` <= 0");
        assert!(p < 1.0, "Binomial::new called with `p` >= 1");
        Binomial { n: n, p: p }
    }
}

impl Distribution<u64> for Binomial {
    fn sample<R: Rng>(&self, rng: &mut R) -> u64 {
        // binomial distribution is symmetrical with respect to p -> 1-p, k -> n-k
        // switch p so that it is less than 0.5 - this allows for lower expected values
        // we will just invert the result at the end
        let p = if self.p <= 0.5 {
            self.p
        } else {
            1.0 - self.p
        };

        // expected value of the sample
        let expected = self.n as f64 * p;

        let result =
            // for low expected values we just simulate n drawings
            if expected < 25.0 {
                let mut lresult = 0.0;
                for _ in 0 .. self.n {
                    if rng.gen::<f64>() < p {
                        lresult += 1.0;
                    }
                }
                lresult
            }
            // high expected value - do the rejection method
            else {
                // prepare some cached values
                let float_n = self.n as f64;
                let ln_fact_n = log_gamma(float_n + 1.0);
                let pc = 1.0 - p;
                let log_p = p.ln();
                let log_pc = pc.ln();
                let sq = (expected * (2.0 * pc)).sqrt();

                let mut lresult;

                loop {
                    let mut comp_dev: f64;
                    // we use the lorentzian distribution as the comparison distribution
                    // f(x) ~ 1/(1+x/^2)
                    loop {
                        // draw from the lorentzian distribution
                        comp_dev = (PI*rng.gen::<f64>()).tan();
                        // shift the peak of the comparison ditribution
                        lresult = expected + sq * comp_dev;
                        // repeat the drawing until we are in the range of possible values
                        if lresult >= 0.0 && lresult < float_n + 1.0 {
                            break;
                        }
                    }

                    // the result should be discrete
                    lresult = lresult.floor();

                    let log_binomial_dist = ln_fact_n - log_gamma(lresult+1.0) -
                        log_gamma(float_n - lresult + 1.0) + lresult*log_p + (float_n - lresult)*log_pc;
                    // this is the binomial probability divided by the comparison probability
                    // we will generate a uniform random value and if it is larger than this,
                    // we interpret it as a value falling out of the distribution and repeat
                    let comparison_coeff = (log_binomial_dist.exp() * sq) * (1.2 * (1.0 + comp_dev*comp_dev));

                    if comparison_coeff >= rng.gen() {
                        break;
                    }
                }

                lresult
            };

        // invert the result for p < 0.5
        if p != self.p {
            self.n - result as u64
        } else {
            result as u64
        }
    }
}

#[cfg(test)]
mod test {
    use distributions::Distribution;
    use super::Binomial;

    #[test]
    fn test_binomial() {
        let binomial = Binomial::new(150, 0.1);
        let mut rng = ::test::rng(123);
        let mut sum = 0;
        for _ in 0..1000 {
            sum += binomial.sample(&mut rng);
        }
        let avg = (sum as f64) / 1000.0;
        println!("Binomial average: {}", avg);
        assert!((avg - 15.0).abs() < 0.5); // not 100% certain, but probable enough
    }

    #[test]
    #[should_panic]
    #[cfg_attr(target_env = "msvc", ignore)]
    fn test_binomial_invalid_lambda_zero() {
        Binomial::new(20, 0.0);
    }
    #[test]
    #[should_panic]
    #[cfg_attr(target_env = "msvc", ignore)]
    fn test_binomial_invalid_lambda_neg() {
        Binomial::new(20, -10.0);
    }
}
