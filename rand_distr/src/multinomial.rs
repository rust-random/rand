// Copyright 2018 Developers of the Rand project.
// Copyright 2013 The Rust Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The multinomial distribution.

use core::usize;

use crate::{Binomial, Distribution};
use num_traits::AsPrimitive;
use rand::Rng;

/// Error type returned from `Multinomial::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// There is a negative weight or Nan
    ProbabilityNegative,
    /// Sum overflows to inf
    SumOverflow,
    /// Sum is zero
    SumZero,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Error::ProbabilityNegative => "One of the weights is negative or Nan",
            Error::SumOverflow => "Sum of weights overflows to inf",
            Error::SumZero => "Sum of weights is zero",
        })
    }
}

/// The [Multinomial](https://en.wikipedia.org/wiki/Multinomial_distribution) distribution `Multinomial(n, w)`.
#[derive(Debug)]
pub struct Multinomial {}

impl Multinomial {
    /// Constructs a new `Multinomial` distribution which samples `K` samples.
    ///
    /// `n` is the number of draws.
    ///
    /// `weights` have to be non negative and will be normalized to 1.
    ///
    /// `K` has to be known at compile time
    pub fn new_const<const K: usize, I>(
        n: I,
        weights: &[f64; K],
    ) -> Result<MultinomialConst<K, I>, Error>
    where
        I: num_traits::PrimInt,
        u64: num_traits::AsPrimitive<I>,
        I: num_traits::AsPrimitive<u64>,
    {
        let all_pos = weights.iter().all(|&x| x >= 0.0);

        if !all_pos {
            return Err(Error::ProbabilityNegative);
        }

        let sum: f64 = weights.iter().sum();

        if !sum.is_finite() {
            return Err(Error::SumOverflow);
        }

        if sum == 0.0 {
            return Err(Error::SumZero);
        }

        return Ok(MultinomialConst::<K, I> {
            n,
            weights: weights,
            sum,
        });
    }

    #[cfg(feature = "alloc")]
    /// Constructs a new `Multinomial` distribution which samples `K` samples.
    ///
    /// `n` is the number of draws.
    ///
    /// `weights` have to be not negative and will be normalized to 1.
    ///
    /// `K` can be specified at runtime
    pub fn new_dyn<I>(n: I, weights: &[f64]) -> Result<MultinomialDyn<'_, I>, Error> {
        let all_pos = weights.iter().all(|&x| x >= 0.0);

        if !all_pos {
            return Err(Error::ProbabilityNegative);
        }

        let sum: f64 = weights.iter().sum();

        if !sum.is_finite() {
            return Err(Error::SumOverflow);
        }

        if sum == 0.0 {
            return Err(Error::SumZero);
        }

        return Ok(MultinomialDyn::<I> {
            n,
            weights: weights,
            sum,
        });
    }
}
/// Multinomial Distribution with compile time known number of categories.
/// Can be created with [Multinomial::new_const].
#[derive(Debug, Clone, PartialEq)]
pub struct MultinomialConst<'a, const K: usize, I> {
    /// number of draws
    n: I,
    /// weights for the multinomial distribution
    weights: &'a [f64; K],
    /// sum of the weights
    sum: f64,
}

#[cfg(feature = "alloc")]
/// Multinomial Distribution with number of categories known at runtime.
/// Can be created with [Multinomial::new_dyn].
#[derive(Debug, Clone, PartialEq)]
pub struct MultinomialDyn<'a, I> {
    /// number of draws
    n: I,
    /// weights for the multinomial distribution
    weights: &'a [f64],
    /// sum of the weights
    sum: f64,
}

/// sum has to be the sum of the weights, this is a performance optimization
fn sample<R: Rng + ?Sized, I: Copy + 'static>(
    rng: &mut R,
    n: I,
    weights: &[f64],
    sum: f64,
    result: &mut [I],
) where
    I: num_traits::PrimInt,
    u64: num_traits::AsPrimitive<I>,
    I: num_traits::AsPrimitive<u64>,
{
    // This follows the binomial approach in "The computer generation of multinomial random variates" by Charles S. Davis

    let mut sum_p = 0.0;
    let mut sum_n: I = 0.as_();

    for k in 0..weights.len() {
        if sum - sum_p <= 0.0 {
            result[k] = 0.as_();
            continue;
        }

        let prob = (weights[k] / (sum - sum_p)).min(1.0);
        let binomial = Binomial::new((n - sum_n).as_(), prob)
            .expect("We know that prob is between 0.0 and 1.0");
        result[k] = binomial.sample(rng).as_();
        sum_n = sum_n + result[k];
        sum_p += weights[k];
    }
}

impl<'a, const K: usize, I> Distribution<[I; K]> for MultinomialConst<'a, K, I>
where
    I: num_traits::PrimInt,
    u64: num_traits::AsPrimitive<I>,
    I: num_traits::AsPrimitive<u64>,
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> [I; K] {
        let mut result = [0.as_(); K];
        sample(rng, self.n, self.weights, self.sum, &mut result);
        result
    }
}

#[cfg(feature = "alloc")]
impl<'a, I> Distribution<alloc::vec::Vec<I>> for MultinomialDyn<'a, I>
where
    I: num_traits::PrimInt,
    u64: num_traits::AsPrimitive<I>,
    I: num_traits::AsPrimitive<u64>,
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> alloc::vec::Vec<I> {
        let mut result = alloc::vec![0.as_(); self.weights.len()];
        sample(rng, self.n, self.weights, self.sum, &mut result);
        result
    }
}

#[cfg(test)]
mod test {

    #[test]
    fn test_multinomial_const() {
        use super::*;

        let n: i32 = 1000;
        let weights = [0.1, 0.2, 0.3, 0.4];
        let mut rng = crate::test::rng(123);
        let multinomial = Multinomial::new_const(n, &weights).unwrap();
        let sample = multinomial.sample(&mut rng);
        assert_eq!(sample.iter().sum::<i32>(), n);
    }

    #[test]
    fn test_almost_zero_dist() {
        use super::*;

        let n: i32 = 1000;
        let weights = [0.0, 0.0, 0.0, 0.000000001];
        let multinomial = Multinomial::new_const(n, &weights).unwrap();
        let sample = multinomial.sample(&mut crate::test::rng(123));
        assert!(sample[3] == n);
    }

    #[test]
    fn test_zero_dist() {
        use super::*;

        let n: i32 = 1000;
        let weights = [0.0, 0.0, 0.0, 0.0];
        let multinomial = Multinomial::new_const(n, &weights);
        assert_eq!(multinomial, Err(Error::SumZero));
    }

    #[test]
    fn test_negative_dist() {
        use super::*;

        let n: i32 = 1000;
        let weights = [0.1, 0.2, 0.3, -0.6];
        let multinomial = Multinomial::new_const(n, &weights);
        assert_eq!(multinomial, Err(Error::ProbabilityNegative));
    }

    #[test]
    fn test_overflow() {
        use super::*;

        let n: i32 = 1000;
        let weights = [f64::MAX, f64::MAX, f64::MAX, f64::MAX];
        let multinomial = Multinomial::new_const(n, &weights);
        assert_eq!(multinomial, Err(Error::SumOverflow));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_multinomial_dyn() {
        use super::*;

        let n = 1000;
        let weights = [0.1, 0.2, 0.3, 0.4];
        let mut rng = crate::test::rng(123);
        let multinomial = Multinomial::new_dyn(n, &weights).unwrap();
        let sample = multinomial.sample(&mut rng);
        assert_eq!(sample.iter().sum::<u64>(), n);
    }
}
