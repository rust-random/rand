//! The geometric distribution.

use crate::{Distribution, Exp, Exp1};
use num_traits::Float;
use rand::Rng;
use std::fmt;

/// The geometric distribution `Geo(p)`.
/// 
/// This is the probability distribution of the number of failures before the
/// first success in a series of Bernoulli trials. It has the density function
/// `f(k) = (1 - p)^k p` for `k >= 0`, where `p` is the probability of success
/// on each trial.
/// 
/// This is the discrete analogue of the [exponential distribution](crate::Exp).
///
/// # Example
///
/// ```
/// use rand_distr::{Geo, Distribution};
///
/// let geo = Geo::new(0.5).unwrap();
/// let x = geo.sample(&mut rand::thread_rng());
/// println!("{} is from a Geo(0.5) distribution", x);
/// ```
#[derive(Copy, Clone, Debug)]
pub struct Geo<F>
where F: Float, Exp1: Distribution<F>
{
    exp: Exp<F>
}

/// Error type returned from `Geo::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// `p < 0 || p > 1` or `nan`
    InvalidProbability,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::InvalidProbability => "p is NaN or outside the interval [0, 1] in geometric distribution",
        })
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}

impl<F> Geo<F>
where F: Float, Exp1: Distribution<F>
{
    /// Construct a new `Geo` with the given shape parameter `p`
    /// (probablity of success on each trial).
    pub fn new(p: F) -> Result<Self, Error> {
        let lambda = -F::ln(F::one() - p);
        match Exp::new(lambda) {
            Ok(exp) => Ok(Geo { exp }),
            Err(_) => Err(Error::InvalidProbability)
        }
    }
}

impl<F> Distribution<u64> for Geo<F>
where F: Float, Exp1: Distribution<F>
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u64 {
        let f = self.exp.sample(rng).floor();
        num_traits::NumCast::from(f).unwrap_or(u64::max_value())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_geo_invalid_p() {
        assert!(Geo::new(f64::NAN).is_err());
        assert!(Geo::new(f64::INFINITY).is_err());
        assert!(Geo::new(f64::NEG_INFINITY).is_err());

        assert!(Geo::new(-0.5).is_err());
        assert!(Geo::new(0.0).is_ok());
        assert!(Geo::new(1.0).is_ok());
        assert!(Geo::new(2.0).is_err());
    }

    fn test_geo_mean_and_variance<R: Rng>(p: f64, rng: &mut R) {
        let distr = Geo::new(p).unwrap();

        let expected_mean = (1.0 - p) / p;
        let expected_variance = (1.0 - p) / (p * p);

        let mut results = [0.0; 1000];
        for i in results.iter_mut() {
            *i = distr.sample(rng) as f64;
        }

        let mean = results.iter().sum::<f64>() / results.len() as f64;
        assert!((mean as f64 - expected_mean).abs() < expected_mean / 20.0);

        let variance =
            results.iter().map(|x| (x - mean) * (x - mean)).sum::<f64>() / results.len() as f64;
        assert!((variance - expected_variance).abs() < expected_variance / 5.0);
    }

    #[test]
    fn test_geometric() {
        let mut rng = crate::test::rng(12345);

        test_geo_mean_and_variance(0.10, &mut rng);
        test_geo_mean_and_variance(0.25, &mut rng);
        test_geo_mean_and_variance(0.50, &mut rng);
        test_geo_mean_and_variance(0.75, &mut rng);
        test_geo_mean_and_variance(0.90, &mut rng);
    }
}