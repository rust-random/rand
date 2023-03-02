// Copyright 2018 Developers of the Rand project.
// Copyright 2013 The Rust Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The dirichlet distribution.
#![cfg(feature = "alloc")]
use num_traits::Float;
use crate::{Distribution, Exp1, Gamma, Open01, StandardNormal};
use rand::Rng;
use core::fmt;
#[cfg(feature = "serde_with")]
use serde_with::serde_as;

/// The Dirichlet distribution `Dirichlet(alpha)`.
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
/// let dirichlet = Dirichlet::new([1.0, 2.0, 3.0]).unwrap();
/// let samples = dirichlet.sample(&mut rand::thread_rng());
/// println!("{:?} is from a Dirichlet([1.0, 2.0, 3.0]) distribution", samples);
/// ```
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[cfg_attr(feature = "serde_with", serde_as)]
#[derive(Clone, Debug, PartialEq)]
pub struct Dirichlet<F, const N: usize>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    /// Concentration parameters (alpha)
    #[cfg_attr(feature = "serde_with", serde_as(as = "[_; N]"))]
    alpha: [F; N],
}

/// Error type returned from `Dirchlet::new`.
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// `alpha.len() < 2`.
    AlphaTooShort,
    /// `alpha <= 0.0` or `nan`.
    AlphaTooSmall,
    /// `size < 2`.
    SizeTooSmall,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::AlphaTooShort | Error::SizeTooSmall => {
                "less than 2 dimensions in Dirichlet distribution"
            }
            Error::AlphaTooSmall => "alpha is not positive in Dirichlet distribution",
        })
    }
}

#[cfg(feature = "std")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "std")))]
impl std::error::Error for Error {}

impl<F, const N: usize> Dirichlet<F, N>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    /// Construct a new `Dirichlet` with the given alpha parameter `alpha`.
    ///
    /// Requires `alpha.len() >= 2`.
    #[inline]
    pub fn new(alpha: [F; N]) -> Result<Dirichlet<F, N>, Error> {
        if N < 2 {
            return Err(Error::AlphaTooShort);
        }
        for &ai in alpha.iter() {
            if !(ai > F::zero()) {
                return Err(Error::AlphaTooSmall);
            }
        }

        Ok(Dirichlet { alpha })
    }
}

impl<F, const N: usize> Distribution<[F; N]> for Dirichlet<F, N>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> [F; N] {
        let mut samples = [F::zero(); N];
        let mut sum = F::zero();

        for (s, &a) in samples.iter_mut().zip(self.alpha.iter()) {
            let g = Gamma::new(a, F::one()).unwrap();
            *s = g.sample(rng);
            sum =  sum + (*s);
        }
        let invacc = F::one() / sum;
        for s in samples.iter_mut() {
            *s = (*s)*invacc;
        }
        samples
    }
}

#[cfg(test)]
mod test {
    use alloc::vec::Vec;
    use super::*;

    #[test]
    fn test_dirichlet() {
        let d = Dirichlet::new([1.0, 2.0, 3.0]).unwrap();
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
        Dirichlet::new([0.5]).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_dirichlet_invalid_alpha() {
        Dirichlet::new([0.1, 0.0, 0.3]).unwrap();
    }

    #[test]
    fn dirichlet_distributions_can_be_compared() {
        assert_eq!(Dirichlet::new([1.0, 2.0]), Dirichlet::new([1.0, 2.0]));
    }
}
