// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The Pareto distribution.

use Rng;
use distributions::{Distribution, OpenClosed01};

/// Samples floating-point numbers according to the Pareto distribution
///
/// # Example
/// ```
/// use rand::prelude::*;
/// use rand::distributions::Pareto;
///
/// let val: f64 = SmallRng::from_entropy().sample(Pareto::new(1., 2.));
/// println!("{}", val);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Pareto {
    scale: f64,
    shape: f64,
}

impl Pareto {
    /// Construct a new Pareto distribution with given `scale` and `shape`.
    ///
    /// # Panics
    ///
    /// `scale` and `shape` have to be non-zero and positive.
    pub fn new(scale: f64, shape: f64) -> Pareto {
        assert!((scale > 0.) & (shape > 0.));
        Pareto { scale, shape }
    }
}

impl Distribution<f64> for Pareto {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> f64 {
        let u: f64 = rng.sample(OpenClosed01);
        self.scale * u.powf(-1.0 / self.shape)
    }
}

#[cfg(test)]
mod tests {
    use distributions::Distribution;
    use super::Pareto;

    #[test]
    #[should_panic]
    fn invalid() {
        Pareto::new(0., 0.);
    }

    #[test]
    fn sample() {
        let d = Pareto::new(1.0, 2.0);
        let mut rng = ::test::rng(1);
        for _ in 0..1000 {
            d.sample(&mut rng);
        }
    }
}
