// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The Pareto distribution.

use rand::Rng;
use crate::{Distribution, OpenClosed01};
use crate::utils::Float;

/// Samples floating-point numbers according to the Pareto distribution
///
/// # Example
/// ```
/// use rand::prelude::*;
/// use rand_distr::Pareto;
///
/// let val: f64 = thread_rng().sample(Pareto::new(1., 2.).unwrap());
/// println!("{}", val);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Pareto<N> {
    scale: N,
    inv_neg_shape: N,
}

/// Error type returned from `Pareto::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// `scale <= 0` or `nan`.
    ScaleTooSmall,
    /// `shape <= 0` or `nan`.
    ShapeTooSmall,
}

impl<N: Float> Pareto<N>
where OpenClosed01: Distribution<N>
{
    /// Construct a new Pareto distribution with given `scale` and `shape`.
    ///
    /// In the literature, `scale` is commonly written as x<sub>m</sub> or k and
    /// `shape` is often written as α.
    pub fn new(scale: N, shape: N) -> Result<Pareto<N>, Error> {
        if !(scale > N::from(0.0)) {
            return Err(Error::ScaleTooSmall);
        }
        if !(shape > N::from(0.0)) {
            return Err(Error::ShapeTooSmall);
        }
        Ok(Pareto { scale, inv_neg_shape: N::from(-1.0) / shape })
    }
}

impl<N: Float> Distribution<N> for Pareto<N>
where OpenClosed01: Distribution<N>
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> N {
        let u: N = OpenClosed01.sample(rng);
        self.scale * u.powf(self.inv_neg_shape)
    }
}

#[cfg(test)]
mod tests {
    use crate::Distribution;
    use super::Pareto;

    #[test]
    #[should_panic]
    fn invalid() {
        Pareto::new(0., 0.).unwrap();
    }

    #[test]
    fn sample() {
        let scale = 1.0;
        let shape = 2.0;
        let d = Pareto::new(scale, shape).unwrap();
        let mut rng = crate::test::rng(1);
        for _ in 0..1000 {
            let r = d.sample(&mut rng);
            assert!(r >= scale);
        }
    }
}
