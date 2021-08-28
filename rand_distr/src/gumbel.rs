// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The Gumbel distribution.

use crate::{Distribution, OpenClosed01};
use core::fmt;
use num_traits::Float;
use rand::Rng;

/// Samples floating-point numbers according to the Gumbel distribution
///
/// # Example
/// ```
/// use rand::prelude::*;
/// use rand_distr::Gumbel;
///
/// let val: f64 = thread_rng().sample(Gumbel::new(1., 10.).unwrap());
/// println!("{}", val);
/// ```
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
pub struct Gumbel<F>
where
    F: Float,
    OpenClosed01: Distribution<F>,
{
    location: F,
    scale: F,
}

/// Error type returned from `Gumbel::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// location is infinite or NaN
    LocationNotValid,
    /// scale is not finite positive number
    ScaleNotValid,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::ScaleNotValid => "scale is not positive and finite in Gumbel distribution",
            Error::LocationNotValid => "location is not finite in Gumbel distribution",
        })
    }
}

#[cfg(feature = "std")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "std")))]
impl std::error::Error for Error {}

impl<F> Gumbel<F>
where
    F: Float,
    OpenClosed01: Distribution<F>,
{
    /// Construct a new `Gumbel` distribution with given `location` and `scale`.
    pub fn new(location: F, scale: F) -> Result<Gumbel<F>, Error> {
        if scale <= F::zero() || scale.is_infinite() || scale.is_nan() {
            return Err(Error::ScaleNotValid);
        }
        if location.is_infinite() || location.is_nan() {
            return Err(Error::LocationNotValid);
        }
        Ok(Gumbel { location, scale })
    }
}

impl<F> Distribution<F> for Gumbel<F>
where
    F: Float,
    OpenClosed01: Distribution<F>,
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> F {
        let x: F = rng.sample(OpenClosed01);
        self.location - self.scale * (-(x).ln()).ln()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic]
    fn test_zero_scale() {
        Gumbel::new(0.0, 0.0).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_infinite_scale() {
        Gumbel::new(0.0, std::f64::INFINITY).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_nan_scale() {
        Gumbel::new(0.0, std::f64::NAN).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_infinite_location() {
        Gumbel::new(std::f64::INFINITY, 1.0).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_nan_location() {
        Gumbel::new(std::f64::NAN, 1.0).unwrap();
    }

    #[test]
    fn test_sample_against_cdf() {
        let scale = 1.0;
        let shape = 2.0;
        let d = Gumbel::new(scale, shape).unwrap();
        let mut rng = crate::test::rng(1);
        for _ in 0..1000 {
            let r = d.sample(&mut rng);
            assert!(r >= 0.);
        }
    }
}
