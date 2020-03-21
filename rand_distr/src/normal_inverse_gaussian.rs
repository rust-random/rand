use crate::{Distribution, Float, InverseGaussian, Standard, StandardNormal};
use rand::Rng;

/// Error type returned from `NormalInverseGaussian::new`
#[derive(Debug, PartialEq)]
pub enum Error {
    /// `alpha <= 0` or `nan`.
    AlphaNegativeOrNull,
    /// `|beta| >= alpha` or `nan`.
    AbsoluteBetaLessThanAlpha,
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
            return Err(Error::AbsoluteBetaLessThanAlpha);
        }

        let gamma = (alpha.powf(N::from(2.)) - beta.powf(N::from(2.))).sqrt();

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
}
