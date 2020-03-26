use crate::{Distribution, Float, Standard, StandardNormal};
use rand::Rng;

/// Error type returned from `InverseGaussian::new`
#[derive(Debug, PartialEq)]
pub enum Error {
    /// `mean <= 0` or `nan`.
    MeanNegativeOrNull,
    /// `shape <= 0` or `nan`.
    ShapeNegativeOrNull,
}

/// The [inverse Gaussian distribution](https://en.wikipedia.org/wiki/Inverse_Gaussian_distribution)
#[derive(Debug)]
pub struct InverseGaussian<N> {
    mean: N,
    shape: N,
}

impl<N: Float> InverseGaussian<N>
where StandardNormal: Distribution<N>
{
    /// Construct a new `InverseGaussian` distribution with the given mean and
    /// shape.
    pub fn new(mean: N, shape: N) -> Result<InverseGaussian<N>, Error> {
        if !(mean > N::from(0.0)) {
            return Err(Error::MeanNegativeOrNull);
        }

        if !(shape > N::from(0.0)) {
            return Err(Error::ShapeNegativeOrNull);
        }

        Ok(Self { mean, shape })
    }
}

impl<N: Float> Distribution<N> for InverseGaussian<N>
where
    StandardNormal: Distribution<N>,
    Standard: Distribution<N>,
{
    fn sample<R>(&self, rng: &mut R) -> N
    where R: Rng + ?Sized {
        let mu = self.mean;
        let l = self.shape;

        let v: N = rng.sample(StandardNormal);
        let y = mu * v * v;

        let mu_2l = mu / (N::from(2.) * l);

        let x = mu + mu_2l * (y - (N::from(4.) * l * y + y * y).sqrt());

        let u: N = rng.gen();

        if u <= mu / (mu + x) {
            return x;
        }

        mu * mu / x
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_inverse_gaussian() {
        let inv_gauss = InverseGaussian::new(1.0, 1.0).unwrap();
        let mut rng = crate::test::rng(210);
        for _ in 0..1000 {
            inv_gauss.sample(&mut rng);
        }
    }

    #[test]
    fn test_inverse_gaussian_invalid_param() {
        assert!(InverseGaussian::new(-1.0, 1.0).is_err());
        assert!(InverseGaussian::new(-1.0, -1.0).is_err());
        assert!(InverseGaussian::new(1.0, -1.0).is_err());
        assert!(InverseGaussian::new(1.0, 1.0).is_ok());
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

        test_samples(InverseGaussian::new(1.0, 3.0).unwrap(), 0f32, &[
            0.9339157, 1.108113, 0.50864697, 0.39849377,
        ]);
        test_samples(InverseGaussian::new(1.0, 3.0).unwrap(), 0f64, &[
            1.0707604954722476,
            0.9628140605340697,
            0.4069687656468226,
            0.660283852985818,
        ]);
    }
}
