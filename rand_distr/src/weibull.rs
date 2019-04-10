// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The Weibull distribution.

use rand::Rng;
use crate::{Distribution, OpenClosed01};

/// Samples floating-point numbers according to the Weibull distribution
///
/// # Example
/// ```
/// use rand::prelude::*;
/// use rand_distr::Weibull;
///
/// let val: f64 = SmallRng::from_entropy().sample(Weibull::new(1., 10.).unwrap());
/// println!("{}", val);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Weibull {
    inv_shape: f64,
    scale: f64,
}

/// Error type returned from `Weibull::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// `scale <= 0` or `nan`.
    ScaleTooSmall,
    /// `shape <= 0` or `nan`.
    ShapeTooSmall,
}

impl Weibull {
    /// Construct a new `Weibull` distribution with given `scale` and `shape`.
    pub fn new(scale: f64, shape: f64) -> Result<Weibull, Error> {
        if !(scale > 0.0) {
            return Err(Error::ScaleTooSmall);
        }
        if !(shape > 0.0) {
            return Err(Error::ShapeTooSmall);
        }
        Ok(Weibull { inv_shape: 1./shape, scale })
    }
}

impl Distribution<f64> for Weibull {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> f64 {
        let x: f64 = rng.sample(OpenClosed01);
        self.scale * (-x.ln()).powf(self.inv_shape)
    }
}

#[cfg(test)]
mod tests {
    use crate::Distribution;
    use super::Weibull;

    #[test]
    #[should_panic]
    fn invalid() {
        Weibull::new(0., 0.).unwrap();
    }

    #[test]
    fn sample() {
        let scale = 1.0;
        let shape = 2.0;
        let d = Weibull::new(scale, shape).unwrap();
        let mut rng = crate::test::rng(1);
        for _ in 0..1000 {
            let r = d.sample(&mut rng);
            assert!(r >= 0.);
        }
    }
}
