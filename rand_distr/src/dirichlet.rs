// Copyright 2018 Developers of the Rand project.
// Copyright 2013 The Rust Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The dirichlet distribution.

use rand::Rng;
use crate::{Distribution, Gamma, StandardNormal, Exp1, Open01};
use crate::utils::Float;

/// The dirichelet distribution `Dirichlet(alpha)`.
///
/// The Dirichlet distribution is a family of continuous multivariate
/// probability distributions parameterized by a vector alpha of positive reals.
/// It is a multivariate generalization of the beta distribution.
///
/// # Example
///
/// ```
/// use rand::prelude::*;
/// use rand_distr::Dirichlet;
///
/// let dirichlet = Dirichlet::new(vec![1.0, 2.0, 3.0]).unwrap();
/// let samples = dirichlet.sample(&mut rand::thread_rng());
/// println!("{:?} is from a Dirichlet([1.0, 2.0, 3.0]) distribution", samples);
/// ```
#[derive(Clone, Debug)]
pub struct Dirichlet<N> {
    /// Concentration parameters (alpha)
    alpha: Vec<N>,
}

/// Error type returned from `Dirchlet::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// `alpha.len() < 2`.
    AlphaTooShort,
    /// `alpha <= 0.0` or `nan`.
    AlphaTooSmall,
    /// `size < 2`.
    SizeTooSmall,
}

impl<N: Float> Dirichlet<N>
where StandardNormal: Distribution<N>, Exp1: Distribution<N>, Open01: Distribution<N>
{
    /// Construct a new `Dirichlet` with the given alpha parameter `alpha`.
    ///
    /// Requires `alpha.len() >= 2`.
    #[inline]
    pub fn new<V: Into<Vec<N>>>(alpha: V) -> Result<Dirichlet<N>, Error> {
        let a = alpha.into();
        if a.len() < 2 {
            return Err(Error::AlphaTooShort);
        }
        for &ai in &a {
            if !(ai > N::from(0.0)) {
                return Err(Error::AlphaTooSmall);
            }
        }

        Ok(Dirichlet { alpha: a })
    }

    /// Construct a new `Dirichlet` with the given shape parameter `alpha` and `size`.
    ///
    /// Requires `size >= 2`.
    #[inline]
    pub fn new_with_size(alpha: N, size: usize) -> Result<Dirichlet<N>, Error> {
        if !(alpha > N::from(0.0)) {
            return Err(Error::AlphaTooSmall);
        }
        if size < 2 {
            return Err(Error::SizeTooSmall);
        }
        Ok(Dirichlet {
            alpha: vec![alpha; size],
        })
    }
}

impl<N: Float> Distribution<Vec<N>> for Dirichlet<N>
where StandardNormal: Distribution<N>, Exp1: Distribution<N>, Open01: Distribution<N>
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<N> {
        let n = self.alpha.len();
        let mut samples = vec![N::from(0.0); n];
        let mut sum = N::from(0.0);

        for (s, &a) in samples.iter_mut().zip(self.alpha.iter()) {
            let g = Gamma::new(a, N::from(1.0)).unwrap();
            *s = g.sample(rng);
            sum += *s;
        }
        let invacc = N::from(1.0) / sum;
        for s in samples.iter_mut() {
            *s *= invacc;
        }
        samples
    }
}

#[cfg(test)]
mod test {
    use super::Dirichlet;
    use crate::Distribution;

    #[test]
    fn test_dirichlet() {
        let d = Dirichlet::new(vec![1.0, 2.0, 3.0]).unwrap();
        let mut rng = crate::test::rng(221);
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
        let d = Dirichlet::new_with_size(alpha, size).unwrap();
        let mut rng = crate::test::rng(221);
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
        Dirichlet::new_with_size(0.5f64, 1).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_dirichlet_invalid_alpha() {
        Dirichlet::new_with_size(0.0f64, 2).unwrap();
    }
}
