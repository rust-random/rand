//! The negative binomial distribution.

use crate::{Distribution, Exp1, Gamma, Open01, Poisson, Standard, StandardNormal};
use core::fmt;
#[allow(unused_imports)]
use num_traits::{Float, FloatConst};
use rand::Rng;

//
// This enum exists because we handle p=1 for NegativeBinomial(r, p).
// When p is 1, the distribution is trivial--the PMF is 1 for k=0 and 0
// elsewhere.  In that case, we don't need to store the Gamma distribution
// instance.
//
#[derive(Copy, Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
enum NegativeBinomialRepr<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    /// Trivial distribution that always generates 0, for the case p=1.
    POne,

    /// The stored Gamma distribution is Gamma(r, (1 - p)/p), where `r` is the
    /// number of successes and `p` is the probability of success.
    PLessThanOne(Gamma<F>),
}

/// The negative binomial distribution `NegativeBinomial(r, p)`.
///
/// The negative binomial distribution is a discrete distribution with two
/// parameters, `r` and `p`.  When `r` is an integer, the negative binomial
/// distribution can be interpreted as the distribution of the number of
/// failures in a sequence of Bernoulli trials that continue until `r`
/// successes occur.  `p` is the probability of success in a single Bernoulli
/// trial.
///
/// `NegativeBinomial` accepts floating point types for `r`.  This is a
/// generalization of the more common case where `r` is an integer.
///
/// The density function of this distribution is
///
/// ```text
///                Γ(k + r)
/// f(k; r, p) = ------------- (1 - p)^k p^r
///              Γ(k + 1) Γ(r)
/// ```
///
/// where Γ(x) is the gamma function.
///
/// When `r` is an integer, the density function is
///
/// ```text
/// f(k; r, p) = C(k + r - 1, k) (1 - p)^k p^r
/// ```
///
/// where `C(m, k)` is the binomial coefficient, read "m choose k".
///
/// Despite being a discrete distribution, the `sample` method of
/// `NegativeBinomial` returns a floating point type.  This is consistent
/// with several other discrete distributions in the `rand_distr` crate.
///
/// # Example
///
/// ```
/// use rand_distr::{Distribution, NegativeBinomial};
///
/// let nb = NegativeBinomial::<f64>::new(10.0, 0.02).unwrap();
/// let v = nb.sample(&mut rand::thread_rng());
/// println!("{} is from a NegativeBinomial(10, 0.02) distribution", v);
/// ```
#[derive(Copy, Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
pub struct NegativeBinomial<F>
where
    F: Float + FloatConst,
    Standard: Distribution<F>,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    repr: NegativeBinomialRepr<F>,
}

/// Error type returned from `NegativeBinomial::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// `r < 0` or `r` is `nan`
    InvalidNumberOfSuccesses,

    /// `p <= 0 || p > 1` or `p` is `nan`
    InvalidProbability,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::InvalidNumberOfSuccesses => "r is NaN or not strictly positive",
            Error::InvalidProbability => "p is NaN or outside the interval (0, 1]",
        })
    }
}

#[cfg(feature = "std")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "std")))]
impl std::error::Error for Error {}

impl<F> NegativeBinomial<F>
where
    F: Float + FloatConst,
    Standard: Distribution<F>,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    /// Construct a new `NegativeBinomial` with the given parameters `r`
    /// (number of successes) and `p` (probability of success on each trial).
    pub fn new(r: F, p: F) -> Result<Self, Error> {
        if !r.is_finite() || r <= F::zero() {
            Err(Error::InvalidNumberOfSuccesses)
        } else if !(p > F::zero() && p <= F::one()) {
            Err(Error::InvalidProbability)
        } else if p == F::one() {
            Ok(NegativeBinomial {
                repr: NegativeBinomialRepr::POne,
            })
        } else {
            Ok(NegativeBinomial {
                repr: NegativeBinomialRepr::PLessThanOne(
                    Gamma::<F>::new(r, (F::one() - p) / p).unwrap(),
                ),
            })
        }
    }
}

impl<F> Distribution<F> for NegativeBinomial<F>
where
    F: Float + FloatConst,
    Standard: Distribution<F>,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> F {
        match &self.repr {
            NegativeBinomialRepr::POne => F::zero(),
            NegativeBinomialRepr::PLessThanOne(gamma) => {
                // The method used here is to generate a Gamma(r, (1-p)/p)
                // variate, and use it as the parameter of Poisson.  See,
                // for example, section X.4.7 of the text *Non-Uniform Random
                // Variate Generation* by Luc Devroye (Springer-Verlag, 1986).
                // The gamma distribution was created in the `new()` method
                // and saved in the NegativeBinomial instance, because it
                // depends on just the parameters `r` and `p`.  We have to
                // create a new Poisson instance for each variate generated.
                Poisson::<F>::new(gamma.sample(rng)).unwrap().sample(rng)
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_nb_invalid_p() {
        assert!(NegativeBinomial::<f64>::new(1.0, core::f64::NAN).is_err());
        assert!(NegativeBinomial::<f64>::new(1.0, core::f64::INFINITY).is_err());
        assert!(NegativeBinomial::<f64>::new(1.0, core::f64::NEG_INFINITY).is_err());

        assert!(NegativeBinomial::<f64>::new(1.0, -0.5).is_err());
        assert!(NegativeBinomial::<f64>::new(1.0, 0.0).is_err());
        assert!(NegativeBinomial::<f64>::new(1.0, 0.2).is_ok());
        assert!(NegativeBinomial::<f64>::new(1.0, 1.0).is_ok());
        assert!(NegativeBinomial::<f64>::new(1.0, 2.0).is_err());
    }

    fn test_nb_mean_and_variance<R: Rng>(r: f64, p: f64, rng: &mut R) {
        let distr = NegativeBinomial::<f64>::new(r, p).unwrap();

        let expected_mean = r * (1.0 - p) / p;
        let expected_variance = r * (1.0 - p) / (p * p);

        let mut results = [0.0; 10000];
        for i in results.iter_mut() {
            *i = distr.sample(rng);
        }

        let mean = results.iter().sum::<f64>() / results.len() as f64;
        // This test is equivalent to requiring that the relative error
        // is less than 0.01.
        assert!((mean - expected_mean).abs() < 0.01 * expected_mean);

        let variance =
            results.iter().map(|x| (x - mean) * (x - mean)).sum::<f64>() / results.len() as f64;
        assert!((variance - expected_variance).abs() < 0.05 * expected_variance);
    }

    #[test]
    fn test_negative_binomial() {
        let mut rng = crate::test::rng(1894736523008208032);

        test_nb_mean_and_variance(8.0, 0.10, &mut rng);
        test_nb_mean_and_variance(200.0, 0.10, &mut rng);
        test_nb_mean_and_variance(8.0, 0.25, &mut rng);
        test_nb_mean_and_variance(4.0, 0.50, &mut rng);
        test_nb_mean_and_variance(3.0, 0.75, &mut rng);
        test_nb_mean_and_variance(10.0, 0.90, &mut rng);
        test_nb_mean_and_variance(1000.0, 0.90, &mut rng);
    }

    fn check_p_one_returns_zero<F>()
    where
        F: Float + FloatConst + core::fmt::Debug,
        Standard: Distribution<F>,
        StandardNormal: Distribution<F>,
        Exp1: Distribution<F>,
        Open01: Distribution<F>,
    {
        // When p is 1, the samples are all 0.
        let mut rng = crate::test::rng(1894736523008208032);
        let nb = NegativeBinomial::<F>::new(F::one(), F::one()).unwrap();
        for _i in 0..10 {
            assert_eq!(nb.sample(&mut rng), F::zero());
        }
    }

    #[test]
    fn test_p_one_returns_zero() {
        check_p_one_returns_zero::<f64>();
        check_p_one_returns_zero::<f32>();
    }

    #[test]
    fn negative_binomial_distributions_can_be_compared() {
        assert_eq!(
            NegativeBinomial::<f64>::new(3.0, 0.25),
            NegativeBinomial::<f64>::new(3.0, 0.25)
        );
    }
}
