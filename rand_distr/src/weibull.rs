// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The Weibull distribution.

use crate::utils::Float;
use crate::{Distribution, OpenClosed01};
use rand::Rng;
use std::{error, fmt};

/// Samples floating-point numbers according to the Weibull distribution
///
/// # Example
/// ```
/// use rand::prelude::*;
/// use rand_distr::Weibull;
///
/// let val: f64 = thread_rng().sample(Weibull::new(1., 10.).unwrap());
/// println!("{}", val);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Weibull<N> {
    inv_shape: N,
    scale: N,
}

/// Error type returned from `Weibull::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// `scale <= 0` or `nan`.
    ScaleTooSmall,
    /// `shape <= 0` or `nan`.
    ShapeTooSmall,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::ScaleTooSmall => "scale is not positive in Weibull distribution",
            Error::ShapeTooSmall => "shape is not positive in Weibull distribution",
        })
    }
}

impl error::Error for Error {}

impl<N: Float> Weibull<N>
where OpenClosed01: Distribution<N>
{
    /// Construct a new `Weibull` distribution with given `scale` and `shape`.
    pub fn new(scale: N, shape: N) -> Result<Weibull<N>, Error> {
        if !(scale > N::from(0.0)) {
            return Err(Error::ScaleTooSmall);
        }
        if !(shape > N::from(0.0)) {
            return Err(Error::ShapeTooSmall);
        }
        Ok(Weibull {
            inv_shape: N::from(1.) / shape,
            scale,
        })
    }
}

impl<N: Float> Distribution<N> for Weibull<N>
where OpenClosed01: Distribution<N>
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> N {
        let x: N = rng.sample(OpenClosed01);
        self.scale * (-x.ln()).powf(self.inv_shape)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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

        test_samples(Weibull::new(1.0, 1.0).unwrap(), 0f32, &[
            0.041495778,
            0.7531094,
            1.4189332,
            0.38386202,
        ]);
        test_samples(Weibull::new(2.0, 0.5).unwrap(), 0f64, &[
            1.1343478702739669,
            0.29470010050655226,
            0.7556151370284702,
            7.877212340241561,
        ]);
    }
}
