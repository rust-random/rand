use crate::{Distribution, Float, InverseGaussian, Standard, StandardNormal};
use rand::Rng;

/// Error type returned from `NormalInverseGaussian::new`
#[derive(Debug, PartialEq)]
pub enum Error {
    /// `alpha <= 0` or `nan`.
    AlphaNegativeOrNull,
    /// `|beta| >= alpha` or `nan`.
    AbsoluteBetaNotLessThanAlpha,
}

/// The [normal-inverse Gaussian distribution](https://en.wikipedia.org/wiki/Normal-inverse_Gaussian_distribution)
#[derive(Debug)]
pub struct NormalInverseGaussian<N> {
    alpha: N,
    beta: N,
    inverse_gaussian: InverseGaussian<N>,
}

impl<N: Float> NormalInverseGaussian<N>
where StandardNormal: Distribution<N>
{
    /// Construct a new `NormalInverseGaussian` distribution with the given alpha (tail heaviness) and
    /// beta (asymmetry) parameters.
    pub fn new(alpha: N, beta: N) -> Result<NormalInverseGaussian<N>, Error> {
        if !(alpha > N::from(0.0)) {
            return Err(Error::AlphaNegativeOrNull);
        }

        if !(beta.abs() < alpha) {
            return Err(Error::AbsoluteBetaNotLessThanAlpha);
        }

        let gamma = (alpha * alpha - beta * beta).sqrt();

        let mu = N::from(1.) / gamma;

        let inverse_gaussian = InverseGaussian::new(mu, N::from(1.)).unwrap();

        Ok(Self {
            alpha,
            beta,
            inverse_gaussian,
        })
    }
}

impl<N: Float> Distribution<N> for NormalInverseGaussian<N>
where
    StandardNormal: Distribution<N>,
    Standard: Distribution<N>,
{
    fn sample<R>(&self, rng: &mut R) -> N
    where R: Rng + ?Sized {
        let inv_gauss = rng.sample(&self.inverse_gaussian);

        self.beta * inv_gauss + inv_gauss.sqrt() * rng.sample(StandardNormal)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_normal_inverse_gaussian() {
        let norm_inv_gauss = NormalInverseGaussian::new(2.0, 1.0).unwrap();
        let mut rng = crate::test::rng(210);
        for _ in 0..1000 {
            norm_inv_gauss.sample(&mut rng);
        }
    }

    #[test]
    fn test_normal_inverse_gaussian_invalid_param() {
        assert!(NormalInverseGaussian::new(-1.0, 1.0).is_err());
        assert!(NormalInverseGaussian::new(-1.0, -1.0).is_err());
        assert!(NormalInverseGaussian::new(1.0, 2.0).is_err());
        assert!(NormalInverseGaussian::new(2.0, 1.0).is_ok());
    }


    #[test]
    fn value_stability() {
        fn test_samples<N: Float + core::fmt::Debug, D: Distribution<N>>(
            distr: D, zero: N, expected: &[N],
        ) {
            let mut rng = crate::test::rng(213);
            let mut buf = [zero; 4];
            for x in &mut buf {
                *x = rng.sample(&distr);
            }
            assert_eq!(buf, expected);
        }

        test_samples(NormalInverseGaussian::new(2.0, 1.0).unwrap(), 0f32, &[
            0.6568966, 1.3744819, 2.216063, 0.11488572,
        ]);
        test_samples(NormalInverseGaussian::new(2.0, 1.0).unwrap(), 0f64, &[
            0.6838707059642927,
            2.4447306460569784,
            0.2361045023235968,
            1.7774534624785319,
        ]);
    }
}
