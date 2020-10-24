//! The hypergeometric distribution.

use crate::Distribution;
use rand::Rng;
use core::fmt;

/// The hypergeometric distribution `Hypergeometric(N, K, n)`.
/// 
/// This is the distribution of successes in samples of size `n` drawn without
/// replacement from a population of size `N` containing `K` success states.
/// It has the density function:
/// `f(k) = binomial(K, k) * binomial(N-K, n-k) / binomial(N, n)`,
/// where `binomial(a, b) = a! / (b! * (a - b)!)`.
/// 
/// The [binomial distribution](crate::Binomial) is the analagous distribution
/// for sampling with replacement. It is a good approximation when the population
/// size is much larger than the sample size.
/// 
/// # Example
/// 
/// ```
/// use rand_distr::{Distribution, Hypergeometric};
///
/// let hypergeo = Hypergeometric::new(60, 24, 7).unwrap();
/// let v = hypergeo.sample(&mut rand::thread_rng());
/// println!("{} is from a hypergeometric distribution", v);
/// ```
#[derive(Copy, Clone, Debug)]
pub struct Hypergeometric {
    total_population_size: u64,
    population_with_feature: u64,
    sample_size: u64,
}

/// Error type returned from `Hypergeometric::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// `population_with_feature > total_population_size`.
    ProbabilityTooLarge,
    /// `sample_size > total_population_size`.
    SampleSizeTooLarge,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::ProbabilityTooLarge => "population_with_feature > total_population_size in geometric distribution",
            Error::SampleSizeTooLarge => "sample_size > total_population_size in geometric distribution",
        })
    }
}

impl Hypergeometric {
    /// Constructs a new `Hypergeometric` with the given shape parameters.
    pub fn new(total_population_size: u64, population_with_feature: u64, sample_size: u64) -> Result<Self, Error> {
        if population_with_feature > total_population_size {
            return Err(Error::ProbabilityTooLarge);
        }

        if sample_size > total_population_size {
            return Err(Error::SampleSizeTooLarge);
        }

        Ok(Hypergeometric { total_population_size, population_with_feature, sample_size })
    }
}

impl Distribution<u64> for Hypergeometric {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u64 {
        // This is exact, but very naive; execution time is linear in `sample_size`.
        // I've found references to a better rejection-based method called H2PEC
        // (published in 1988 by Kachitvichyanukul and Schmeiser), but no existing
        // implementations, pseudo-code or even an informal explanation of it, so...

        let mut n = self.total_population_size;
        let mut k = self.population_with_feature;

        let mut result = 0;
        for _ in 0..self.sample_size {
            let x = rng.gen_range(0..n);
            
            if x < k {
                k -= 1;
                result += 1;
            }

            n -= 1;
        }

        result
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_hypergeometric_invalid_params() {
        assert!(Hypergeometric::new(100, 101, 5).is_err());
        assert!(Hypergeometric::new(100, 10, 101).is_err());
        assert!(Hypergeometric::new(100, 101, 101).is_err());
        assert!(Hypergeometric::new(100, 10, 5).is_ok());
    }

    fn test_hypergeometric_mean_and_variance<R: Rng>(n: u64, k: u64, s: u64, rng: &mut R)
    {
        let distr = Hypergeometric::new(n, k, s).unwrap();

        let expected_mean = s as f64 * k as f64 / n as f64;
        let expected_variance = {
            let numerator = (s * k * (n - k) * (n - s)) as f64;
            let denominator = (n * n * (n - 1)) as f64;
            numerator / denominator
        };

        let mut results = [0.0; 1000];
        for i in results.iter_mut() {
            *i = distr.sample(rng) as f64;
        }

        let mean = results.iter().sum::<f64>() / results.len() as f64;
        assert!((mean as f64 - expected_mean).abs() < expected_mean / 50.0);

        let variance =
            results.iter().map(|x| (x - mean) * (x - mean)).sum::<f64>() / results.len() as f64;
        assert!((variance - expected_variance).abs() < expected_variance / 10.0);
    }

    #[test]
    fn test_hypergeometric() {
        let mut rng = crate::test::rng(737);

        test_hypergeometric_mean_and_variance(1000, 500, 100, &mut rng);
        test_hypergeometric_mean_and_variance(500, 400, 30, &mut rng);
        test_hypergeometric_mean_and_variance(100, 30, 7, &mut rng);
        test_hypergeometric_mean_and_variance(60, 24, 7, &mut rng);
        test_hypergeometric_mean_and_variance(40, 17, 7, &mut rng);
    }
}