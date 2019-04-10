// Copyright 2018 Developers of the Rand project.
// Copyright 2016-2017 The Rust Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The binomial distribution.

use rand::Rng;
use crate::{Distribution, Cauchy};
use crate::utils::log_gamma;

/// The binomial distribution `Binomial(n, p)`.
///
/// This distribution has density function:
/// `f(k) = n!/(k! (n-k)!) p^k (1-p)^(n-k)` for `k >= 0`.
///
/// # Example
///
/// ```
/// use rand_distr::{Binomial, Distribution};
///
/// let bin = Binomial::new(20, 0.3).unwrap();
/// let v = bin.sample(&mut rand::thread_rng());
/// println!("{} is from a binomial distribution", v);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Binomial {
    /// Number of trials.
    n: u64,
    /// Probability of success.
    p: f64,
}

/// Error type returned from `Binomial::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// `p < 0` or `nan`.
    ProbabilityTooSmall,
    /// `p > 1`.
    ProbabilityTooLarge,
}

impl Binomial {
    /// Construct a new `Binomial` with the given shape parameters `n` (number
    /// of trials) and `p` (probability of success).
    pub fn new(n: u64, p: f64) -> Result<Binomial, Error> {
        if !(p >= 0.0) {
            return Err(Error::ProbabilityTooSmall);
        }
        if !(p <= 1.0) {
            return Err(Error::ProbabilityTooLarge);
        }
        Ok(Binomial { n, p })
    }
}

impl Distribution<u64> for Binomial {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u64 {
        // Handle these values directly.
        if self.p == 0.0 {
            return 0;
        } else if self.p == 1.0 {
            return self.n;
        }

        // binomial distribution is symmetrical with respect to p -> 1-p, k -> n-k
        // switch p so that it is less than 0.5 - this allows for lower expected values
        // we will just invert the result at the end
        let p = if self.p <= 0.5 {
            self.p
        } else {
            1.0 - self.p
        };

        let result;

        // For small n * min(p, 1 - p), the BINV algorithm based on the inverse
        // transformation of the binomial distribution is more efficient:
        //
        // Voratas Kachitvichyanukul and Bruce W. Schmeiser. 1988. Binomial
        // random variate generation. Commun. ACM 31, 2 (February 1988),
        // 216-222. http://dx.doi.org/10.1145/42372.42381
        if (self.n as f64) * p < 10. && self.n <= (::std::i32::MAX as u64) {
            let q = 1. - p;
            let s = p / q;
            let a = ((self.n + 1) as f64) * s;
            let mut r = q.powi(self.n as i32);
            let mut u: f64 = rng.gen();
            let mut x = 0;
            while u > r as f64 {
                u -= r;
                x += 1;
                r *= a / (x as f64) - s;
            }
            result = x;
        } else {
            // FIXME: Using the BTPE algorithm is probably faster.

            // prepare some cached values
            let float_n = self.n as f64;
            let ln_fact_n = log_gamma(float_n + 1.0);
            let pc = 1.0 - p;
            let log_p = p.ln();
            let log_pc = pc.ln();
            let expected = self.n as f64 * p;
            let sq = (expected * (2.0 * pc)).sqrt();
            let mut lresult;

            // we use the Cauchy distribution as the comparison distribution
            // f(x) ~ 1/(1+x^2)
            let cauchy = Cauchy::new(0.0, 1.0).unwrap();
            loop {
                let mut comp_dev: f64;
                loop {
                    // draw from the Cauchy distribution
                    comp_dev = rng.sample(cauchy);
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
            result = lresult as u64;
        }

        // invert the result for p < 0.5
        if p != self.p {
            self.n - result
        } else {
            result
        }
    }
}

#[cfg(test)]
mod test {
    use rand::Rng;
    use crate::Distribution;
    use super::Binomial;

    fn test_binomial_mean_and_variance<R: Rng>(n: u64, p: f64, rng: &mut R) {
        let binomial = Binomial::new(n, p).unwrap();

        let expected_mean = n as f64 * p;
        let expected_variance = n as f64 * p * (1.0 - p);

        let mut results = [0.0; 1000];
        for i in results.iter_mut() { *i = binomial.sample(rng) as f64; }

        let mean = results.iter().sum::<f64>() / results.len() as f64;
        assert!((mean as f64 - expected_mean).abs() < expected_mean / 50.0);

        let variance =
            results.iter().map(|x| (x - mean) * (x - mean)).sum::<f64>()
            / results.len() as f64;
        assert!((variance - expected_variance).abs() < expected_variance / 10.0);
    }

    #[test]
    fn test_binomial() {
        let mut rng = crate::test::rng(351);
        test_binomial_mean_and_variance(150, 0.1, &mut rng);
        test_binomial_mean_and_variance(70, 0.6, &mut rng);
        test_binomial_mean_and_variance(40, 0.5, &mut rng);
        test_binomial_mean_and_variance(20, 0.7, &mut rng);
        test_binomial_mean_and_variance(20, 0.5, &mut rng);
    }

    #[test]
    fn test_binomial_end_points() {
        let mut rng = crate::test::rng(352);
        assert_eq!(rng.sample(Binomial::new(20, 0.0).unwrap()), 0);
        assert_eq!(rng.sample(Binomial::new(20, 1.0).unwrap()), 20);
    }

    #[test]
    #[should_panic]
    fn test_binomial_invalid_lambda_neg() {
        Binomial::new(20, -10.0).unwrap();
    }
}
