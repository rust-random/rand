// Copyright 2016-2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The Cauchy distribution.

use Rng;
use distributions::{Distribution, Open01};

/// The Cauchy distribution `Cauchy(median, scale)`.
///
/// This distribution has a density function:
/// `f(x) = 1 / (pi * scale * (1 + ((x - median) / scale)^2))`
///
/// # Example
///
/// ```
/// use rand::distributions::{Cauchy, Distribution};
///
/// let cau = Cauchy::new(2.0, 5.0);
/// let v = cau.sample(&mut rand::thread_rng());
/// println!("{} is from a Cauchy(2, 5) distribution", v);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Cauchy {
    median: f64,
    scale: f64
}

impl Cauchy {
    /// Construct a new `Cauchy` with the given shape parameters
    /// `median` the peak location and `scale` the scale factor.
    /// Panics if `scale <= 0`.
    pub fn new(median: f64, scale: f64) -> Cauchy {
        assert!(scale > 0.0, "Cauchy::new called with scale factor <= 0");
        Cauchy {
            median,
            scale
        }
    }
}

impl Distribution<f64> for Cauchy {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> f64 {
        // Algorithim from the paper:
        //     Efficient table-free sampling methods for the exponential, Cauchy, and normal distributions
        //     by Joachim H. Ahrens and Ulrich Dieter

        // ~magic values~
        // these are precomputed values for numerically approximating a Cauchy quantile function
        let a = 0.6380_6313_6607_7803;
        let b = 0.5959_4860_6052_9070;
        let q = 0.9339_9629_5760_3656;
        let w = 0.2488_7022_8008_3841;
        let c = 0.6366_1977_2367_5813;
        let d = 0.5972_9975_9353_9963;
        let h = 0.0214_9490_0457_0452;
        let p = 4.9125_0139_5303_3204;

        let mut std_cau: f64;
        let mut uni: f64 = rng.sample(Open01);
        let mut x = uni - 0.5;
        let mut s = w - x*x;
        if s > 0.0 {
            std_cau = x * ((c / s) + d);
        }
        else {
            // fall back to rejection method
            loop {
                uni = rng.sample(Open01);
                x = uni - 0.5;
                s = 0.25 - x*x;
                std_cau = x * ((a / s) + b);
                let uni1: f64 = rng.sample(Open01);
                let test = s*s * ((1.0 + std_cau*std_cau) * (h * uni1 + p) - q) + s;
                if test <= 0.5 {
                    break;
                }
            }
        }
        let result = self.median + self.scale * std_cau; // shift and scale according to parameters
        result
    }
}

#[cfg(test)]
mod test {
    use distributions::Distribution;
    use super::Cauchy;

    fn median(mut numbers: &mut [f64]) -> f64 {
        sort(&mut numbers);
        let mid = numbers.len() / 2;
        numbers[mid]
    }

    fn sort(numbers: &mut [f64]) {
        numbers.sort_by(|a, b| a.partial_cmp(b).unwrap());
    }

    #[test]
    fn test_cauchy_median() {
        let cauchy = Cauchy::new(5.0, 10.0);
        let mut rng = ::test::rng(321);
        let mut numbers: [f64; 1000] = [0.0; 1000];
        for i in 0..1000 {
            numbers[i] = cauchy.sample(&mut rng);
        }
        let median = median(&mut numbers);
        println!("Cauchy median: {}", median);
        assert!((median - 5.0).abs() < 0.5); // not 100% certain, but probable enough
    }

    #[test]
    fn test_cauchy_mean() {
        let cauchy = Cauchy::new(5.0, 10.0);
        let mut rng = ::test::rng(322);
        let mut sum = 0.0;
        for _ in 0..1000 {
            sum += cauchy.sample(&mut rng);
        }
        let mean = sum / 1000.0;
        println!("Cauchy mean: {}", mean);
        // for a Cauchy distribution the mean should not converge
        assert!((mean - 5.0).abs() > 0.5); // not 100% certain, but probable enough
    }

    #[test]
    #[should_panic]
    fn test_cauchy_invalid_scale_zero() {
        Cauchy::new(0.0, 0.0);
    }

    #[test]
    #[should_panic]
    fn test_cauchy_invalid_scale_neg() {
        Cauchy::new(0.0, -10.0);
    }
}
