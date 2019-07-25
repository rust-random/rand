// Copyright 2018 Developers of the Rand project.
// Copyright 2016-2017 The Rust Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The Cauchy distribution.

use rand::Rng;
use crate::{Distribution, Standard};
use crate::utils::Float;

/// The Cauchy distribution `Cauchy(median, scale)`.
///
/// This distribution has a density function:
/// `f(x) = 1 / (pi * scale * (1 + ((x - median) / scale)^2))`
///
/// # Example
///
/// ```
/// use rand_distr::{Cauchy, Distribution};
///
/// let cau = Cauchy::new(2.0, 5.0).unwrap();
/// let v = cau.sample(&mut rand::thread_rng());
/// println!("{} is from a Cauchy(2, 5) distribution", v);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Cauchy<N> {
    median: N,
    scale: N,
}

/// Error type returned from `Cauchy::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// `scale <= 0` or `nan`.
    ScaleTooSmall,
}

impl<N: Float> Cauchy<N>
where Standard: Distribution<N>
{
    /// Construct a new `Cauchy` with the given shape parameters
    /// `median` the peak location and `scale` the scale factor.
    pub fn new(median: N, scale: N) -> Result<Cauchy<N>, Error> {
        if !(scale > N::from(0.0)) {
            return Err(Error::ScaleTooSmall);
        }
        Ok(Cauchy {
            median,
            scale
        })
    }
}

impl<N: Float> Distribution<N> for Cauchy<N>
where Standard: Distribution<N>
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> N {
        // sample from [0, 1)
        let x = Standard.sample(rng);
        // get standard cauchy random number
        // note that π/2 is not exactly representable, even if x=0.5 the result is finite
        let comp_dev = (N::pi() * x).tan();
        // shift and scale according to parameters
        self.median + self.scale * comp_dev
    }
}

#[cfg(test)]
mod test {
    use crate::Distribution;
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
    fn test_cauchy_averages() {
        // NOTE: given that the variance and mean are undefined,
        // this test does not have any rigorous statistical meaning.
        let cauchy = Cauchy::new(10.0, 5.0).unwrap();
        let mut rng = crate::test::rng(123);
        let mut numbers: [f64; 1000] = [0.0; 1000];
        let mut sum = 0.0;
        for i in 0..1000 {
            numbers[i] = cauchy.sample(&mut rng);
            sum += numbers[i];
        }
        let median = median(&mut numbers);
        println!("Cauchy median: {}", median);
        assert!((median - 10.0).abs() < 0.4); // not 100% certain, but probable enough
        let mean = sum / 1000.0;
        println!("Cauchy mean: {}", mean);
        // for a Cauchy distribution the mean should not converge
        assert!((mean - 10.0).abs() > 0.4); // not 100% certain, but probable enough
    }

    #[test]
    #[should_panic]
    fn test_cauchy_invalid_scale_zero() {
        Cauchy::new(0.0, 0.0).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_cauchy_invalid_scale_neg() {
        Cauchy::new(0.0, -10.0).unwrap();
    }
}
