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

// evaluate fact(numerator.0)*fact(numerator.1) / fact(denominator.0)*fact(denominator.1)
fn fraction_of_products_of_factorials(numerator: (u64, u64), denominator: (u64, u64)) -> f64 {
    let min_top = u64::min(numerator.0, numerator.1);
    let min_bottom = u64::min(denominator.0, denominator.1);
    // the factorial of this will cancel out:
    let min_all = u64::min(min_top, min_bottom);

    let max_top = u64::max(numerator.0, numerator.1);
    let max_bottom = u64::max(denominator.0, denominator.1);
    let max_all = u64::max(max_top, max_bottom);

    let mut result = 1.0;
    for i in (min_all + 1)..=max_all {
        if i <= min_top {
            result *= i as f64;
        }
        
        if i <= min_bottom {
            result /= i as f64;
        }
        
        if i <= max_top {
            result *= i as f64;
        }
        
        if i <= max_bottom {
            result /= i as f64;
        }
    }
    
    result
}

impl Distribution<u64> for Hypergeometric {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u64 {
        // set-up constants as function of original parameters
        let n = self.total_population_size;
        let (mut sign_x, mut offset_x) = (1, 0);
        let (n1, n2) = {
            // switch around success and failure states if necessary to ensure n1 <= n2
            let population_without_feature = n - self.population_with_feature;
            if self.population_with_feature > population_without_feature {
                sign_x = -1;
                offset_x = self.sample_size as i64;
                (population_without_feature, self.population_with_feature)
            } else {
                (self.population_with_feature, population_without_feature)
            }
        };
        // when sampling more than half the total population, take the smaller
        // group as sampled instead (we can then return n1-x instead):
        let k = if self.sample_size <= n / 2 {
            self.sample_size
        } else {
            offset_x += n1 as i64 * sign_x;
            sign_x *= -1;
            n - self.sample_size
        };

        // Algorithm H2PE has bounded runtime only if `M - max(0, k-n2) >= 10`,
        // where `M` is the mode of the distribution.
        // Use algorithm HIN for the remaining parameter space.
        // 
        // Voratas Kachitvichyanukul and Bruce W. Schmeiser. 1985. Computer
        // generation of hypergeometric random variates.
        // J. Statist. Comput. Simul. Vol.22 (August 1985), 127-145
        // https://www.researchgate.net/publication/233212638
        const HIN_THRESHOLD: f64 = 10.0;
        let m = ((k + 1) as f64 * (n1 + 1) as f64 / (n + 2) as f64).floor();
        if m - f64::max(0.0, k as f64 - n2 as f64) < HIN_THRESHOLD {
            let (mut p, mut x) = if k < n2 {
                (fraction_of_products_of_factorials((n2, n - k), (n, n2 - k)), 0)
            } else {
                (fraction_of_products_of_factorials((n1, k), (n, k - n2)), k - n2)
            };

            assert!(p.is_finite());
            let mut u = rng.gen::<f64>();
            while u > p && x < k { // the paper erroneously uses `until n < p`, which doesn't make any sense
                u -= p;
                p *= ((n1 as i64 - x as i64) * (k as i64 - x as i64)) as f64;
                p /= ((x as i64 + 1) * (n2 as i64 - k as i64 + 1 + x as i64)) as f64;
                x += 1;
            }

            return (offset_x + sign_x * x as i64) as u64;
        }

        unimplemented!("Algorithm H2PE")
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

        // exercise algorithm HIN:
        test_hypergeometric_mean_and_variance(500, 400, 30, &mut rng);
        test_hypergeometric_mean_and_variance(250, 200, 230, &mut rng);
        test_hypergeometric_mean_and_variance(100, 20, 6, &mut rng);
        test_hypergeometric_mean_and_variance(50, 10, 47, &mut rng);

        // exercise algorithm H2PE
        test_hypergeometric_mean_and_variance(1000, 500, 100, &mut rng);
    }
}