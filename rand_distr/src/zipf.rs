// Copyright 2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The Zeta and related distributions.

use num_traits::Float;
use crate::{Distribution, Standard};
use rand::{Rng, distributions::OpenClosed01};
use core::fmt;

/// Samples floating-point numbers according to the zeta distribution.
///
/// The zeta distribution is a limit of the [`Zipf`] distribution.
///
/// # Example
/// ```
/// use rand::prelude::*;
/// use rand_distr::Zeta;
///
/// let val: f64 = thread_rng().sample(Zeta::new(1.5).unwrap());
/// println!("{}", val);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Zeta<F>
where F: Float, Standard: Distribution<F>, OpenClosed01: Distribution<F>
{
    a_minus_1: F,
    b: F,
}

/// Error type returned from `Zeta::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZetaError {
    /// `a <= 1` or `nan`.
    ATooSmall,
}

impl fmt::Display for ZetaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            ZetaError::ATooSmall => "a <= 1 or is NaN in Zeta distribution",
        })
    }
}

#[cfg(feature = "std")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "std")))]
impl std::error::Error for ZetaError {}

impl<F> Zeta<F>
where F: Float, Standard: Distribution<F>, OpenClosed01: Distribution<F>
{
    /// Construct a new `Zeta` distribution with given `a` parameter.
    #[inline]
    pub fn new(a: F) -> Result<Zeta<F>, ZetaError> {
        if !(a > F::one()) {
            return Err(ZetaError::ATooSmall);
        }
        let a_minus_1 = a - F::one();
        let two = F::one() + F::one();
        Ok(Zeta {
            a_minus_1,
            b: two.powf(a_minus_1),
        })
    }
}

impl<F> Distribution<F> for Zeta<F>
where F: Float, Standard: Distribution<F>, OpenClosed01: Distribution<F>
{
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> F {
        // This is based on the numpy implementation.
        loop {
            let u = rng.sample(OpenClosed01);
            let v = rng.sample(Standard);
            let x = u.powf(-F::one() / self.a_minus_1).floor();

            if x < F::one() {
                continue;
            }

            let t = (F::one() + F::one() / x).powf(self.a_minus_1);
            if v * x * (t - F::one()) / (self.b - F::one()) <= t / self.b {
                return x;
            }
        }
    }
}

/// Samples floating-point numbers according to the Zipf distribution.
///
/// The samples follow Zipf's law: The frequency of each sample is inversely
/// proportional to a power of its frequency rank.
///
/// For large `n`, this converges to the [`Zeta`] distribution.
///
/// For `s = 0`, this becomes a uniform distribution.
///
/// # Example
/// ```
/// use rand::prelude::*;
/// use rand_distr::Zipf;
///
/// let val: f64 = thread_rng().sample(Zipf::new(10, 1.5).unwrap());
/// println!("{}", val);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Zipf<F>
where F: Float, Standard: Distribution<F> {
    n: F,
    s: F,
    t: F,
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
#[cfg_attr(doc_cfg, doc(cfg(feature = "std")))]
impl std::error::Error for ZipfError {}

impl<F> Zipf<F>
where F: Float, Standard: Distribution<F> {
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
        let n = F::from(n).unwrap();  // This does not fail.
        let t = if s != F::one() {
            (n.powf(F::one() - s) - s) / (F::one() - s)
        } else {
            F::one() + n.ln()
        };
        Ok(Zipf {
            n, s, t
        })
    }

    /// Inverse cumulative density function
    #[inline]
    fn inv_cdf(&self, p: F) -> F {
        let one = F::one();
        let pt = p * self.t;
        if pt <= one {
            pt
        } else if self.s != F::one() {
            (pt * (one - self.s) + self.s).powf(one / (one - self.s))
        } else {
            pt.exp()
        }
    }
}

impl<F> Distribution<F> for Zipf<F>
where F: Float, Standard: Distribution<F>
{
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> F {
        let one = F::one();
        loop {
            let inv_b = self.inv_cdf(rng.sample(Standard));
            let x = (inv_b + one).floor();
            let mut ratio = x.powf(-self.s) * self.t;
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

    fn test_samples<F: Float + core::fmt::Debug, D: Distribution<F>>(
        distr: D, zero: F, expected: &[F],
    ) {
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
        Zeta::new(core::f64::NAN).unwrap();
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
    fn zeta_value_stability() {
        test_samples(Zeta::new(1.5).unwrap(), 0f32, &[
            1.0, 2.0, 1.0, 1.0,
        ]);
        test_samples(Zeta::new(2.0).unwrap(), 0f64, &[
            2.0, 1.0, 1.0, 1.0,
        ]);
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
        Zipf::new(10, core::f64::NAN).unwrap();
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
        let d = Zipf::new(core::u64::MAX, 1.5).unwrap();
        let mut rng = crate::test::rng(2);
        for _ in 0..1000 {
            let r = d.sample(&mut rng);
            assert!(r >= 1.);
        }
        // TODO: verify that this is a zeta distribution
    }

    #[test]
    fn zipf_value_stability() {
        test_samples(Zipf::new(10, 0.5).unwrap(), 0f32, &[
            10.0, 2.0, 6.0, 7.0
        ]);
        test_samples(Zipf::new(10, 2.0).unwrap(), 0f64, &[
            1.0, 2.0, 3.0, 2.0
        ]);
    }
}
