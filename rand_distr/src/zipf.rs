// Copyright 2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The Zeta and related distributions.

use crate::{Distribution, Standard};
use core::fmt;
use num_traits::Float;
use rand::{distributions::OpenClosed01, Rng};

/// The [Zeta distribution](https://en.wikipedia.org/wiki/Zeta_distribution) `Zeta(s)`.
///
/// The [Zeta distribution](https://en.wikipedia.org/wiki/Zeta_distribution)
/// is a discrete probability distribution with parameter `s`.
/// It is a special case of the [`Zipf`] distribution with `n = ∞`.
/// It is also known as the discrete Pareto, Riemann-Zeta, Zipf, or Zipf–Estoup distribution.
///
/// # Density function
///
/// `f(k) = k^(-s) / ζ(s)` for `k >= 1`, where `ζ` is the
/// [Riemann zeta function](https://en.wikipedia.org/wiki/Riemann_zeta_function).
///
/// # Plot
///
/// The following plot illustrates the zeta distribution for various values of `s`.
///
/// ![Zeta distribution](https://raw.githubusercontent.com/rust-random/charts/main/charts/zeta.svg)
///
/// # Example
/// ```
/// use rand::prelude::*;
/// use rand_distr::Zeta;
///
/// let val: f64 = thread_rng().sample(Zeta::new(1.5).unwrap());
/// println!("{}", val);
/// ```
///
/// # Notes
///
/// The zeta distribution has no upper limit. Sampled values may be infinite.
/// In particular, a value of infinity might be returned for the following
/// reasons:
/// 1. it is the best representation in the type `F` of the actual sample.
/// 2. to prevent infinite loops for very small `s`.
///
/// # Implementation details
///
/// We are using the algorithm from
/// [Non-Uniform Random Variate Generation](https://doi.org/10.1007/978-1-4613-8643-8),
/// Section 6.1, page 551.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Zeta<F>
where
    F: Float,
    Standard: Distribution<F>,
    OpenClosed01: Distribution<F>,
{
    s_minus_1: F,
    b: F,
}

/// Error type returned from `Zeta::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZetaError {
    /// `s <= 1` or `nan`.
    STooSmall,
}

impl fmt::Display for ZetaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            ZetaError::STooSmall => "s <= 1 or is NaN in Zeta distribution",
        })
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ZetaError {}

impl<F> Zeta<F>
where
    F: Float,
    Standard: Distribution<F>,
    OpenClosed01: Distribution<F>,
{
    /// Construct a new `Zeta` distribution with given `s` parameter.
    #[inline]
    pub fn new(s: F) -> Result<Zeta<F>, ZetaError> {
        if !(s > F::one()) {
            return Err(ZetaError::STooSmall);
        }
        let s_minus_1 = s - F::one();
        let two = F::one() + F::one();
        Ok(Zeta {
            s_minus_1,
            b: two.powf(s_minus_1),
        })
    }
}

impl<F> Distribution<F> for Zeta<F>
where
    F: Float,
    Standard: Distribution<F>,
    OpenClosed01: Distribution<F>,
{
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> F {
        loop {
            let u = rng.sample(OpenClosed01);
            let x = u.powf(-F::one() / self.s_minus_1).floor();
            debug_assert!(x >= F::one());
            if x.is_infinite() {
                // For sufficiently small `s`, `x` will always be infinite,
                // which is rejected, resulting in an infinite loop. We avoid
                // this by always returning infinity instead.
                return x;
            }

            let t = (F::one() + F::one() / x).powf(self.s_minus_1);

            let v = rng.sample(Standard);
            if v * x * (t - F::one()) * self.b <= t * (self.b - F::one()) {
                return x;
            }
        }
    }
}

/// The Zipf (Zipfian) distribution `Zipf(n, s)`.
///
/// The samples follow [Zipf's law](https://en.wikipedia.org/wiki/Zipf%27s_law):
/// The frequency of each sample from a finite set of size `n` is inversely
/// proportional to a power of its frequency rank (with exponent `s`).
///
/// For large `n`, this converges to the [`Zeta`](crate::Zeta) distribution.
///
/// For `s = 0`, this becomes a [`uniform`](crate::Uniform) distribution.
///
/// # Plot
///
/// The following plot illustrates the Zipf distribution for `n = 10` and
/// various values of `s`.
///
/// ![Zipf distribution](https://raw.githubusercontent.com/rust-random/charts/main/charts/zipf.svg)
///
/// # Example
/// ```
/// use rand::prelude::*;
/// use rand_distr::Zipf;
///
/// let val: f64 = thread_rng().sample(Zipf::new(10, 1.5).unwrap());
/// println!("{}", val);
/// ```
///
/// # Implementation details
///
/// Implemented via [rejection sampling](https://en.wikipedia.org/wiki/Rejection_sampling),
/// due to Jason Crease[1].
///
/// [1]: https://jasoncrease.medium.com/rejection-sampling-the-zipf-distribution-6b359792cffa
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Zipf<F>
where
    F: Float,
    Standard: Distribution<F>,
{
    s: F,
    t: F,
    q: F,
}

/// Error type returned from `Zipf::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZipfError {
    /// `s < 0` or `nan`.
    STooSmall,
    /// `n < 1`.
    NTooSmall,
}

impl fmt::Display for ZipfError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            ZipfError::STooSmall => "s < 0 or is NaN in Zipf distribution",
            ZipfError::NTooSmall => "n < 1 in Zipf distribution",
        })
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ZipfError {}

impl<F> Zipf<F>
where
    F: Float,
    Standard: Distribution<F>,
{
    /// Construct a new `Zipf` distribution for a set with `n` elements and a
    /// frequency rank exponent `s`.
    ///
    /// For large `n`, rounding may occur to fit the number into the float type.
    #[inline]
    pub fn new(n: u64, s: F) -> Result<Zipf<F>, ZipfError> {
        if !(s >= F::zero()) {
            return Err(ZipfError::STooSmall);
        }
        if n < 1 {
            return Err(ZipfError::NTooSmall);
        }
        let n = F::from(n).unwrap(); // This does not fail.
        let q = if s != F::one() {
            // Make sure to calculate the division only once.
            F::one() / (F::one() - s)
        } else {
            // This value is never used.
            F::zero()
        };
        let t = if s != F::one() {
            (n.powf(F::one() - s) - s) * q
        } else {
            F::one() + n.ln()
        };
        debug_assert!(t > F::zero());
        Ok(Zipf { s, t, q })
    }

    /// Inverse cumulative density function
    #[inline]
    fn inv_cdf(&self, p: F) -> F {
        let one = F::one();
        let pt = p * self.t;
        if pt <= one {
            pt
        } else if self.s != one {
            (pt * (one - self.s) + self.s).powf(self.q)
        } else {
            (pt - one).exp()
        }
    }
}

impl<F> Distribution<F> for Zipf<F>
where
    F: Float,
    Standard: Distribution<F>,
{
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> F {
        let one = F::one();
        loop {
            let inv_b = self.inv_cdf(rng.sample(Standard));
            let x = (inv_b + one).floor();
            let mut ratio = x.powf(-self.s);
            if x > one {
                ratio = ratio * inv_b.powf(self.s)
            };

            let y = rng.sample(Standard);
            if y < ratio {
                return x;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_samples<F: Float + fmt::Debug, D: Distribution<F>>(distr: D, zero: F, expected: &[F]) {
        let mut rng = crate::test::rng(213);
        let mut buf = [zero; 4];
        for x in &mut buf {
            *x = rng.sample(&distr);
        }
        assert_eq!(buf, expected);
    }

    #[test]
    #[should_panic]
    fn zeta_invalid() {
        Zeta::new(1.).unwrap();
    }

    #[test]
    #[should_panic]
    fn zeta_nan() {
        Zeta::new(f64::NAN).unwrap();
    }

    #[test]
    fn zeta_sample() {
        let a = 2.0;
        let d = Zeta::new(a).unwrap();
        let mut rng = crate::test::rng(1);
        for _ in 0..1000 {
            let r = d.sample(&mut rng);
            assert!(r >= 1.);
        }
    }

    #[test]
    fn zeta_small_a() {
        let a = 1. + 1e-15;
        let d = Zeta::new(a).unwrap();
        let mut rng = crate::test::rng(2);
        for _ in 0..1000 {
            let r = d.sample(&mut rng);
            assert!(r >= 1.);
        }
    }

    #[test]
    fn zeta_value_stability() {
        test_samples(Zeta::new(1.5).unwrap(), 0f32, &[1.0, 2.0, 1.0, 1.0]);
        test_samples(Zeta::new(2.0).unwrap(), 0f64, &[2.0, 1.0, 1.0, 1.0]);
    }

    #[test]
    #[should_panic]
    fn zipf_s_too_small() {
        Zipf::new(10, -1.).unwrap();
    }

    #[test]
    #[should_panic]
    fn zipf_n_too_small() {
        Zipf::new(0, 1.).unwrap();
    }

    #[test]
    #[should_panic]
    fn zipf_nan() {
        Zipf::new(10, f64::NAN).unwrap();
    }

    #[test]
    fn zipf_sample() {
        let d = Zipf::new(10, 0.5).unwrap();
        let mut rng = crate::test::rng(2);
        for _ in 0..1000 {
            let r = d.sample(&mut rng);
            assert!(r >= 1.);
        }
    }

    #[test]
    fn zipf_sample_s_1() {
        let d = Zipf::new(10, 1.).unwrap();
        let mut rng = crate::test::rng(2);
        for _ in 0..1000 {
            let r = d.sample(&mut rng);
            assert!(r >= 1.);
        }
    }

    #[test]
    fn zipf_sample_s_0() {
        let d = Zipf::new(10, 0.).unwrap();
        let mut rng = crate::test::rng(2);
        for _ in 0..1000 {
            let r = d.sample(&mut rng);
            assert!(r >= 1.);
        }
        // TODO: verify that this is a uniform distribution
    }

    #[test]
    fn zipf_sample_large_n() {
        let d = Zipf::new(u64::MAX, 1.5).unwrap();
        let mut rng = crate::test::rng(2);
        for _ in 0..1000 {
            let r = d.sample(&mut rng);
            assert!(r >= 1.);
        }
        // TODO: verify that this is a zeta distribution
    }

    #[test]
    fn zipf_value_stability() {
        test_samples(Zipf::new(10, 0.5).unwrap(), 0f32, &[10.0, 2.0, 6.0, 7.0]);
        test_samples(Zipf::new(10, 2.0).unwrap(), 0f64, &[1.0, 2.0, 3.0, 2.0]);
    }

    #[test]
    fn zipf_distributions_can_be_compared() {
        assert_eq!(Zipf::new(1, 2.0), Zipf::new(1, 2.0));
    }

    #[test]
    fn zeta_distributions_can_be_compared() {
        assert_eq!(Zeta::new(1.0), Zeta::new(1.0));
    }
}
