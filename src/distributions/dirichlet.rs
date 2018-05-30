// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The dirichlet distribution.

use Rng;
use distributions::Distribution;
use distributions::gamma::Gamma;

/// The dirichelet distribution `Dirichlet(alpha)`.
///
/// The Dirichlet distribution } is a family of continuous multivariate probability distributions parameterized by
/// a vector alpha of positive reals
/// It is a multivariate generalization of the beta distribution.
///
/// # Example
///
/// ```
/// use rand::prelude::*;
/// use rand::distributions::Dirichlet;
///
/// let dirichlet = Dirichlet::new(&vec![1.0, 2.0, 3.0]);
/// let samples = dirichlet.sample(&mut rand::thread_rng());
/// println!("{:?} is from a Dirichlet([1.0, 2.0, 3.0]) distribution", samples);
/// ```

#[derive(Clone, Debug)]
pub struct Dirichlet {
    /// Concentration parameters (alpha)
    alpha: Vec<f64>,
}

impl Dirichlet {
    /// Construct a new `Dirichlet` with the given alpha parameter
    /// `alpha`. Panics if `alpha.len() < 2`.
    #[inline]
    pub fn new(alpha: &[f64]) -> Dirichlet {
        assert!(
            alpha.len() > 1,
            "Dirichlet::new called with `alpha` with length <  2"
        );
        for i in 0..alpha.len() {
            assert!(
                alpha[i] > 0.0,
                "Dirichlet::new called with `alpha`  <=  0.0"
            );
        }

        Dirichlet {
            alpha: alpha.to_vec(),
        }
    }

    /// Construct a new `Dirichlet` with the given shape parameter and size
    /// `alpha`. Panics if `alpha <= 0.0`.
    /// `size` . Panic if `size < 2`
    #[inline]
    pub fn new_with_param(alpha: f64, size: usize) -> Dirichlet {
        assert!(alpha > 0.0, "Dirichlet::new called with `alpha`  <=  0.0");
        assert!(size > 1, "Dirichlet::new called with `size`  <=  1");
        Dirichlet {
            alpha: vec![alpha; size],
        }
    }
}

impl Distribution<Vec<f64>> for Dirichlet {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<f64> {
        let n = self.alpha.len();
        let mut samples = vec![0.0f64; n];
        let mut sum = 0.0f64;

        for i in 0..n {
            let g = Gamma::new(self.alpha[i], 1.0);
            samples[i] = g.sample(rng);
            sum += samples[i];
        }
        let invacc = 1.0 / sum;
        for i in 0..n {
            samples[i] *= invacc;
        }
        samples
    }
}

#[cfg(test)]
mod test {
    use super::Dirichlet;
    use distributions::Distribution;

    #[test]
    fn test_dirichlet() {
        let d = Dirichlet::new(&vec![1.0, 2.0, 3.0]);
        let mut rng = ::test::rng(221);
        let samples = d.sample(&mut rng);
        let _: Vec<f64> = samples
            .into_iter()
            .map(|x| {
                assert!(x > 0.0);
                x
            })
            .collect();
    }

    #[test]
    fn test_dirichlet_with_param() {
        let alpha = 0.5f64;
        let size = 2;
        let d = Dirichlet::new_with_param(alpha, size);
        let mut rng = ::test::rng(221);
        let samples = d.sample(&mut rng);
        let _: Vec<f64> = samples
            .into_iter()
            .map(|x| {
                assert!(x > 0.0);
                x
            })
            .collect();
    }

    #[test]
    #[should_panic]
    fn test_dirichlet_invalid_length() {
        Dirichlet::new_with_param(0.5f64, 1);
    }

    #[test]
    #[should_panic]
    fn test_dirichlet_invalid_alpha() {
        Dirichlet::new_with_param(0.0f64, 2);
    }
}
