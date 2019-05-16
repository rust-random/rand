// Copyright 2018 Developers of the Rand project.
// Copyright 2016-2017 The Rust Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The Poisson distribution.

use rand::Rng;
use crate::{Distribution, Cauchy, Standard};
use crate::utils::Float;

/// The Poisson distribution `Poisson(lambda)`.
///
/// This distribution has a density function:
/// `f(k) = lambda^k * exp(-lambda) / k!` for `k >= 0`.
///
/// # Example
///
/// ```
/// use rand_distr::{Poisson, Distribution};
///
/// let poi = Poisson::new(2.0).unwrap();
/// let v: u64 = poi.sample(&mut rand::thread_rng());
/// println!("{} is from a Poisson(2) distribution", v);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Poisson<N> {
    lambda: N,
    // precalculated values
    exp_lambda: N,
    log_lambda: N,
    sqrt_2lambda: N,
    magic_val: N,
}

/// Error type returned from `Poisson::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// `lambda <= 0` or `nan`.
    ShapeTooSmall,
}

impl<N: Float> Poisson<N>
where Standard: Distribution<N>
{
    /// Construct a new `Poisson` with the given shape parameter
    /// `lambda`.
    pub fn new(lambda: N) -> Result<Poisson<N>, Error> {
        if !(lambda > N::from(0.0)) {
            return Err(Error::ShapeTooSmall);
        }
        let log_lambda = lambda.ln();
        Ok(Poisson {
            lambda,
            exp_lambda: (-lambda).exp(),
            log_lambda,
            sqrt_2lambda: (N::from(2.0) * lambda).sqrt(),
            magic_val: lambda * log_lambda - (N::from(1.0) + lambda).log_gamma(),
        })
    }
}

impl<N: Float> Distribution<N> for Poisson<N>
where Standard: Distribution<N>
{
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> N {
        // using the algorithm from Numerical Recipes in C

        // for low expected values use the Knuth method
        if self.lambda < N::from(12.0) {
            let mut result = N::from(0.);
            let mut p = N::from(1.0);
            while p > self.exp_lambda {
                p *= rng.gen::<N>();
                result += N::from(1.);
            }
            result - N::from(1.)
        }
        // high expected values - rejection method
        else {
            // we use the Cauchy distribution as the comparison distribution
            // f(x) ~ 1/(1+x^2)
            let cauchy = Cauchy::new(N::from(0.0), N::from(1.0)).unwrap();
            let mut result;

            loop {
                let mut comp_dev;

                loop {
                    // draw from the Cauchy distribution
                    comp_dev = rng.sample(cauchy);
                    // shift the peak of the comparison ditribution
                    result = self.sqrt_2lambda * comp_dev + self.lambda;
                    // repeat the drawing until we are in the range of possible values
                    if result >= N::from(0.0) {
                        break;
                    }
                }
                // now the result is a random variable greater than 0 with Cauchy distribution
                // the result should be an integer value
                result = result.floor();

                // this is the ratio of the Poisson distribution to the comparison distribution
                // the magic value scales the distribution function to a range of approximately 0-1
                // since it is not exact, we multiply the ratio by 0.9 to avoid ratios greater than 1
                // this doesn't change the resulting distribution, only increases the rate of failed drawings
                let check = N::from(0.9) * (N::from(1.0) + comp_dev * comp_dev)
                    * (result * self.log_lambda - (N::from(1.0) + result).log_gamma() - self.magic_val).exp();

                // check with uniform random value - if below the threshold, we are within the target distribution
                if rng.gen::<N>() <= check {
                    break;
                }
            }
            result
        }
    }
}

impl<N: Float> Distribution<u64> for Poisson<N>
where Standard: Distribution<N>
{
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u64 {
        let result: N = self.sample(rng);
        result.to_u64().unwrap()
    }
}

#[cfg(test)]
mod test {
    use crate::Distribution;
    use super::Poisson;

    #[test]
    fn test_poisson_10() {
        let poisson = Poisson::new(10.0).unwrap();
        let mut rng = crate::test::rng(123);
        let mut sum_u64 = 0;
        let mut sum_f64 = 0.;
        for _ in 0..1000 {
            let s_u64: u64 = poisson.sample(&mut rng);
            let s_f64: f64 = poisson.sample(&mut rng);
            sum_u64 += s_u64;
            sum_f64 += s_f64;
        }
        let avg_u64 = (sum_u64 as f64) / 1000.0;
        let avg_f64 = sum_f64 / 1000.0;
        println!("Poisson averages: {} (u64)  {} (f64)", avg_u64, avg_f64);
        for &avg in &[avg_u64, avg_f64] {
            assert!((avg - 10.0).abs() < 0.5); // not 100% certain, but probable enough
        }
    }

    #[test]
    fn test_poisson_15() {
        // Take the 'high expected values' path
        let poisson = Poisson::new(15.0).unwrap();
        let mut rng = crate::test::rng(123);
        let mut sum_u64 = 0;
        let mut sum_f64 = 0.;
        for _ in 0..1000 {
            let s_u64: u64 = poisson.sample(&mut rng);
            let s_f64: f64 = poisson.sample(&mut rng);
            sum_u64 += s_u64;
            sum_f64 += s_f64;
        }
        let avg_u64 = (sum_u64 as f64) / 1000.0;
        let avg_f64 = sum_f64 / 1000.0;
        println!("Poisson average: {} (u64)  {} (f64)", avg_u64, avg_f64);
        for &avg in &[avg_u64, avg_f64] {
            assert!((avg - 15.0).abs() < 0.5); // not 100% certain, but probable enough
        }
    }

    #[test]
    fn test_poisson_10_f32() {
        let poisson = Poisson::new(10.0f32).unwrap();
        let mut rng = crate::test::rng(123);
        let mut sum_u64 = 0;
        let mut sum_f32 = 0.;
        for _ in 0..1000 {
            let s_u64: u64 = poisson.sample(&mut rng);
            let s_f32: f32 = poisson.sample(&mut rng);
            sum_u64 += s_u64;
            sum_f32 += s_f32;
        }
        let avg_u64 = (sum_u64 as f32) / 1000.0;
        let avg_f32 = sum_f32 / 1000.0;
        println!("Poisson averages: {} (u64)  {} (f32)", avg_u64, avg_f32);
        for &avg in &[avg_u64, avg_f32] {
            assert!((avg - 10.0).abs() < 0.5); // not 100% certain, but probable enough
        }
    }

    #[test]
    fn test_poisson_15_f32() {
        // Take the 'high expected values' path
        let poisson = Poisson::new(15.0f32).unwrap();
        let mut rng = crate::test::rng(123);
        let mut sum_u64 = 0;
        let mut sum_f32 = 0.;
        for _ in 0..1000 {
            let s_u64: u64 = poisson.sample(&mut rng);
            let s_f32: f32 = poisson.sample(&mut rng);
            sum_u64 += s_u64;
            sum_f32 += s_f32;
        }
        let avg_u64 = (sum_u64 as f32) / 1000.0;
        let avg_f32 = sum_f32 / 1000.0;
        println!("Poisson average: {} (u64)  {} (f32)", avg_u64, avg_f32);
        for &avg in &[avg_u64, avg_f32] {
            assert!((avg - 15.0).abs() < 0.5); // not 100% certain, but probable enough
        }
    }

    #[test]
    #[should_panic]
    fn test_poisson_invalid_lambda_zero() {
        Poisson::new(0.0).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_poisson_invalid_lambda_neg() {
        Poisson::new(-10.0).unwrap();
    }
}
