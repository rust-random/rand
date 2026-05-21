// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The Cauchy distribution `Cauchy(x_0, γ)`.

use crate::distr::Distribution;
use crate::{Rng, RngExt};
use core::fmt;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// The [Cauchy distribution](https://en.wikipedia.org/wiki/Cauchy_distribution) `Cauchy(x_0, γ)`.
///
/// The Cauchy distribution is a continuous probability distribution with
/// location parameter `x_0` (median) and scale parameter `γ > 0` (half-width
/// at half-maximum). It has no finite mean or variance.
///
/// # Plot
///
/// The following plot shows the Cauchy distribution with `x_0 = 0` and
/// `γ = 1` (the standard Cauchy distribution).
///
/// # Example
///
/// ```rust
/// use rand::distr::{Cauchy, Distribution};
///
/// let d = Cauchy::new(0.0, 1.0).unwrap();
/// let v = d.sample(&mut rand::rng());
/// println!("{} is from a Cauchy distribution", v);
/// ```
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Cauchy {
    median: f64,
    scale: f64,
}

/// Error type returned from [`Cauchy::new`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CauchyError {
    /// `scale <= 0` or `scale` is NaN.
    InvalidScale,
    /// `median` is infinite or NaN.
    InvalidMedian,
}

impl fmt::Display for CauchyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            CauchyError::InvalidScale => "scale is not positive and finite in Cauchy distribution",
            CauchyError::InvalidMedian => "median is not finite in Cauchy distribution",
        })
    }
}

impl core::error::Error for CauchyError {}

impl Cauchy {
    /// Construct a new `Cauchy` with the given `median` (`x_0`) and `scale` (`γ`).
    ///
    /// # Errors
    ///
    /// Returns [`CauchyError::InvalidMedian`] if `median` is infinite or NaN,
    /// or [`CauchyError::InvalidScale`] if `scale` is not strictly positive and finite.
    #[inline]
    pub fn new(median: f64, scale: f64) -> Result<Cauchy, CauchyError> {
        if !median.is_finite() {
            return Err(CauchyError::InvalidMedian);
        }
        if !(scale > 0.0) || !scale.is_finite() {
            return Err(CauchyError::InvalidScale);
        }
        Ok(Cauchy { median, scale })
    }

    /// Returns the median (`x_0`) of the distribution.
    #[inline]
    pub fn median(&self) -> f64 {
        self.median
    }

    /// Returns the scale (`γ`) of the distribution.
    #[inline]
    pub fn scale(&self) -> f64 {
        self.scale
    }
}

impl Distribution<f64> for Cauchy {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> f64 {
        loop {
            let u: f64 = 2.0 * rng.random::<f64>() - 1.0;
            let v: f64 = 2.0 * rng.random::<f64>() - 1.0;
            if u * u + v * v > 1.0 || v == 0.0 {
                continue;
            }
            return self.median + self.scale * u / v;
        }
    }
}

#[cfg(test)]
mod test {
    use std::{println, vec::Vec};

    use super::*;
    use crate::RngExt;

    #[test]
    fn test_new_valid() {
        assert!(Cauchy::new(0.0, 1.0).is_ok());
        assert!(Cauchy::new(-5.0, 0.1).is_ok());
    }

    #[test]
    fn test_new_invalid_scale() {
        assert_eq!(Cauchy::new(0.0, 0.0), Err(CauchyError::InvalidScale));
        assert_eq!(Cauchy::new(0.0, -1.0), Err(CauchyError::InvalidScale));
        assert_eq!(Cauchy::new(0.0, f64::NAN), Err(CauchyError::InvalidScale));
        assert_eq!(
            Cauchy::new(0.0, f64::INFINITY),
            Err(CauchyError::InvalidScale)
        );
    }

    #[test]
    fn test_new_invalid_median() {
        assert_eq!(Cauchy::new(f64::NAN, 1.0), Err(CauchyError::InvalidMedian));
        assert_eq!(
            Cauchy::new(f64::INFINITY, 1.0),
            Err(CauchyError::InvalidMedian)
        );
        assert_eq!(
            Cauchy::new(f64::NEG_INFINITY, 1.0),
            Err(CauchyError::InvalidMedian)
        );
    }

    #[test]
    fn test_accessors() {
        let d = Cauchy::new(2.0, 3.0).unwrap();
        assert_eq!(d.median(), 2.0);
        assert_eq!(d.scale(), 3.0);
    }

    #[test]
    #[cfg(feature = "serde")]
    fn test_serializing_deserializing_cauchy() {
        let distr = Cauchy::new(0.0, 1.0).unwrap();
        let de: Cauchy = postcard::from_bytes(&postcard::to_allocvec(&distr).unwrap()).unwrap();
        assert_eq!(distr, de);
    }

    #[test]
    fn test_distr() {
        let mut rng = crate::test::rng(1);
        let distr = Cauchy::new(0.0, 1.0).unwrap();

        const N: usize = 100_000;
        let mut values: Vec<f64> = Vec::new();
        for _ in 0..N {
            values.push(rng.sample(distr));
        }
        values.sort_by(|a, b| a.partial_cmp(b).unwrap());

        // Calculate the Kolmogorov-Smirnoff divergence between the
        // empirical and expected distributions, and check it's small.
        let mut d0 = 0.0;
        for (i, &x) in values.iter().enumerate() {
            let p = (i as f64) / (N as f64);
            let q = x.atan() / std::f64::consts::PI + 0.5;
            let d = (p - q).abs();
            if d > d0 {
                d0 = d;
            }
        }
        assert!(d0 < 0.005);
    }

    #[test]
    fn value_stability() {
        let mut rng = crate::test::rng(1);
        let distr = Cauchy::new(0.0, 1.0).unwrap();
        let mut buf = [0.0f64; 10];
        for x in &mut buf {
            *x = rng.sample(distr);
        }
        // Fill in expected values once sample() is implemented.
        let expected: [f64; 10] = [
            -0.18291029299250308,
            -101.0791569450233,
            0.491799631323629,
            1.5187358196195335,
            -0.4600057220965164,
            0.4052753943925359,
            1.7684714852626602,
            5.167567490120088,
            37.10022546727608,
            -3.533827480127306,
        ];
        assert_eq!(buf, expected);
        for (got, exp) in buf.iter().zip(expected.iter()) {
            println!("got = {}, exp = {}", got, exp);
            assert!((got - exp).abs() < 1e-6);
        }
    }
}
