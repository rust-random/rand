//! The geometric distribution.

use crate::{Distribution, Exp, Exp1};
use num_traits::Float;
use rand::Rng;
use core::fmt;

/// The geometric distribution `Geometric(p)` bounded to `[0, u64::MAX]`.
/// 
/// This is the probability distribution of the number of failures before the
/// first success in a series of Bernoulli trials. It has the density function
/// `f(k) = (1 - p)^k p` for `k >= 0`, where `p` is the probability of success
/// on each trial.
/// 
/// This is the discrete analogue of the [exponential distribution](crate::Exp).
/// 
/// Note that [`StandardGeometric`](crate::StandardGeometric) is an optimised
/// implementation for `p = 0.5`.
///
/// # Example
///
/// ```
/// use rand_distr::{Geometric, Distribution};
///
/// let geo = Geometric::new(0.25).unwrap();
/// let v = geo.sample(&mut rand::thread_rng());
/// println!("{} is from a Geometric(0.25) distribution", v);
/// ```
#[derive(Copy, Clone, Debug)]
pub struct Geometric<F>
where F: Float, Exp1: Distribution<F>
{
    exp: Exp<F>
}

/// Error type returned from `Geometric::new`.
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

impl<F> Geometric<F>
where F: Float, Exp1: Distribution<F>
{
    /// Construct a new `Geometric` with the given shape parameter `p`
    /// (probablity of success on each trial).
    pub fn new(p: F) -> Result<Self, Error> {
        let lambda = -F::ln(F::one() - p);
        match Exp::new(lambda) {
            Ok(exp) => Ok(Geometric { exp }),
            Err(_) => Err(Error::InvalidProbability)
        }
    }
}

impl<F> Distribution<u64> for Geometric<F>
where F: Float, Exp1: Distribution<F>
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u64 {
        let f = self.exp.sample(rng).floor();
        num_traits::NumCast::from(f).unwrap_or(u64::max_value())
    }
}

/// Samples integers according to the geometric distribution with success
/// probability `p = 0.5`. This is equivalent to `Geometeric::new(0.5)`,
/// but faster.
/// 
/// See [`Geometric`](crate::Geometric) for the general geometric distribution.
/// 
/// Implemented via iterated [Rng::gen::<u64>().leading_ones()].
/// 
/// # Example
/// ```
/// use rand::prelude::*;
/// use rand_distr::StandardGeometric;
/// 
/// let v = StandardGeometric.sample(&mut thread_rng());
/// println!("{} is from a Geometric(0.5) distribution", v);
/// ```
#[derive(Copy, Clone, Debug)]
pub struct StandardGeometric;

impl Distribution<u64> for StandardGeometric {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u64 {
        let mut result = 0;
        loop {
            let x = rng.gen::<u64>().leading_ones() as u64;
            result += x;
            if x < 64 { break; }
        }
        result
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_geo_invalid_p() {
        assert!(Geometric::new(core::f64::NAN).is_err());
        assert!(Geometric::new(core::f64::INFINITY).is_err());
        assert!(Geometric::new(core::f64::NEG_INFINITY).is_err());

        assert!(Geometric::new(-0.5).is_err());
        assert!(Geometric::new(0.0).is_ok());
        assert!(Geometric::new(1.0).is_ok());
        assert!(Geometric::new(2.0).is_err());
    }

    fn test_geo_mean_and_variance<R: Rng>(p: f64, rng: &mut R) {
        let distr = Geometric::new(p).unwrap();

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

    #[test]
    fn test_standard_geometric() {
        let mut rng = crate::test::rng(54321);

        let distr = StandardGeometric;
        let expected_mean = 1.0;
        let expected_variance = 2.0;

        let mut results = [0.0; 1000];
        for i in results.iter_mut() {
            *i = distr.sample(&mut rng) as f64;
        }

        let mean = results.iter().sum::<f64>() / results.len() as f64;
        assert!((mean as f64 - expected_mean).abs() < expected_mean / 50.0);

        let variance =
            results.iter().map(|x| (x - mean) * (x - mean)).sum::<f64>() / results.len() as f64;
        assert!((variance - expected_variance).abs() < expected_variance / 10.0);
    }
}