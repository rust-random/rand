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
use crate::{Beta, Distribution, Exp1, Gamma, Open01, StandardNormal};
use alloc::{boxed::Box, vec, vec::Vec};
use core::fmt;
use num_traits::{Float, NumCast};
use rand::Rng;

#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
struct DirichletFromGamma<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    samplers: Box<[Gamma<F>]>,
}

impl<F> DirichletFromGamma<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    // Construct a new `Dirichlet` with the given alpha parameter `alpha`.
    //
    // This function is part of a private implementation detail.
    // It assumes that the input is correct, so no validation is done.
    #[inline]
    fn new(alpha: &[F]) -> DirichletFromGamma<F> {
        let gamma_dists = alpha
            .iter()
            .map(|a| Gamma::new(*a, F::one()).unwrap())
            .collect::<Vec<Gamma<F>>>()
            .into_boxed_slice();
        DirichletFromGamma {
            samplers: gamma_dists,
        }
    }
}

impl<F> Distribution<Vec<F>> for DirichletFromGamma<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<F> {
        let n = self.samplers.len();
        let mut samples = vec![F::zero(); n];
        let mut sum = F::zero();
        for (s, g) in samples.iter_mut().zip(self.samplers.iter()) {
            *s = g.sample(rng);
            sum = sum + (*s);
        }
        let invacc = F::one() / sum;
        for s in samples.iter_mut() {
            *s = (*s) * invacc;
        }
        samples
    }
}

#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
struct DirichletFromBeta<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    samplers: Box<[Beta<F>]>,
}

impl<F> DirichletFromBeta<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    // Construct a new `Dirichlet` with the given alpha parameter `alpha`.
    //
    // This function is part of a private implementation detail.
    // It assumes that the input is correct, so no validation is done.
    #[inline]
    fn new(alpha: &[F]) -> DirichletFromBeta<F> {
        // Form the right-to-left cumulative sum of alpha, exluding the
        // first element of alpha.  E.g. if alpha = [a0, a1, a2, a3], then
        // after the call to `alpha_sum_rl.reverse()` below, alpha_sum_rl
        // will hold [a1+a2+a3, a2+a3, a3].
        let mut alpha_sum_rl: Vec<F> = alpha
            .iter()
            .skip(1)
            .rev()
            // scan does the cumulative sum
            .scan(F::zero(), |sum, x| {
                *sum = *sum + *x;
                Some(*sum)
            })
            .collect();
        alpha_sum_rl.reverse();
        let beta_dists = alpha
            .iter()
            .zip(alpha_sum_rl.iter())
            .map(|t| Beta::new(*t.0, *t.1).unwrap())
            .collect::<Vec<Beta<F>>>()
            .into_boxed_slice();
        DirichletFromBeta {
            samplers: beta_dists,
        }
    }
}

impl<F> Distribution<Vec<F>> for DirichletFromBeta<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<F> {
        let n = self.samplers.len();
        let mut samples = vec![F::zero(); n + 1];
        let mut acc = F::one();

        for (s, beta) in samples.iter_mut().zip(self.samplers.iter()) {
            let beta_sample = beta.sample(rng);
            *s = acc * beta_sample;
            acc = acc * (F::one() - beta_sample);
        }
        samples[n] = acc;
        samples
    }
}

#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
enum DirichletRepr<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    /// Dirichlet distribution that generates samples using the gamma distribution.
    FromGamma(DirichletFromGamma<F>),

    /// Dirichlet distribution that generates samples using the beta distribution.
    FromBeta(DirichletFromBeta<F>),
}

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
/// let dirichlet = Dirichlet::new(&[1.0, 2.0, 3.0]).unwrap();
/// let samples = dirichlet.sample(&mut rand::thread_rng());
/// println!("{:?} is from a Dirichlet([1.0, 2.0, 3.0]) distribution", samples);
/// ```
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde1", derive(serde::Serialize, serde::Deserialize))]
pub struct Dirichlet<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    repr: DirichletRepr<F>,
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

impl<F> Dirichlet<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    /// Construct a new `Dirichlet` with the given alpha parameter `alpha`.
    ///
    /// Requires `alpha.len() >= 2`, and each value in `alpha` must be positive.
    #[inline]
    pub fn new(alpha: &[F]) -> Result<Dirichlet<F>, Error> {
        if alpha.len() < 2 {
            return Err(Error::AlphaTooShort);
        }
        for &ai in alpha.iter() {
            if !(ai > F::zero()) {
                return Err(Error::AlphaTooSmall);
            }
        }

        if alpha.iter().all(|x| *x <= NumCast::from(0.1).unwrap()) {
            // All the values in alpha are less than 0.1.
            Ok(Dirichlet {
                repr: DirichletRepr::FromBeta(DirichletFromBeta::new(alpha)),
            })
        } else {
            Ok(Dirichlet {
                repr: DirichletRepr::FromGamma(DirichletFromGamma::new(alpha)),
            })
        }
    }

    /// Construct a new `Dirichlet` with the given shape parameter `alpha` and `size`.
    ///
    /// Requires `alpha > 0` and  `size >= 2`.
    #[inline]
    pub fn new_with_size(alpha: F, size: usize) -> Result<Dirichlet<F>, Error> {
        if !(alpha > F::zero()) {
            return Err(Error::AlphaTooSmall);
        }
        if size < 2 {
            return Err(Error::SizeTooSmall);
        }
        Ok(Dirichlet::new(vec![alpha; size].as_slice()).unwrap())
    }
}

impl<F> Distribution<Vec<F>> for Dirichlet<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Vec<F> {
        match &self.repr {
            DirichletRepr::FromGamma(dirichlet) => dirichlet.sample(rng),
            DirichletRepr::FromBeta(dirichlet) => dirichlet.sample(rng),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    //
    // Check that the means of the components of n samples from
    // the Dirichlet distribution agree with the expected means
    // with a relative tolerance of rtol.
    //
    // This is a crude statistical test, but it will catch egregious
    // mistakes.  It will also also fail if any samples contain nan.
    //
    fn check_dirichlet_means(alpha: &Vec<f64>, n: i32, rtol: f64, seed: u64) {
        let d = Dirichlet::new(&alpha).unwrap();
        let alpha_len = alpha.len();
        let mut rng = crate::test::rng(seed);
        let mut sums = vec![0.0; alpha_len];
        for _ in 0..n {
            let samples = d.sample(&mut rng);
            for i in 0..alpha_len {
                sums[i] += samples[i];
            }
        }
        let sample_mean: Vec<f64> = sums.iter().map(|x| x / n as f64).collect();
        let alpha_sum: f64 = alpha.iter().sum();
        let expected_mean: Vec<f64> = alpha.iter().map(|x| x / alpha_sum).collect();
        for i in 0..alpha_len {
            assert_almost_eq!(sample_mean[i], expected_mean[i], rtol);
        }
    }

    #[test]
    fn test_dirichlet() {
        let d = Dirichlet::new(&[1.0, 2.0, 3.0]).unwrap();
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
    fn test_dirichlet_means() {
        // Check the means of 20000 samples for several different alphas.
        let alpha_set = vec![
            vec![0.5, 0.25],
            vec![123.0, 75.0],
            vec![2.0, 2.5, 5.0, 7.0],
            vec![0.1, 8.0, 1.0, 2.0, 2.0, 0.85, 0.05, 12.5],
        ];
        let n = 20000;
        let rtol = 2e-2;
        let seed = 1317624576693539401;
        for alpha in alpha_set {
            check_dirichlet_means(&alpha, n, rtol, seed);
        }
    }

    #[test]
    fn test_dirichlet_means_very_small_alpha() {
        // With values of alpha that are all 0.001, check that the means of the
        // components of 10000 samples are within 1% of the expected means.
        // With the sampling method based on gamma variates, this test would
        // fail, with about 10% of the samples containing nan.
        let alpha = vec![0.001, 0.001, 0.001];
        let n = 10000;
        let rtol = 1e-2;
        let seed = 1317624576693539401;
        check_dirichlet_means(&alpha, n, rtol, seed);
    }

    #[test]
    fn test_dirichlet_means_small_alpha() {
        // With values of alpha that are all less than 0.1, check that the
        // means of the components of 150000 samples are within 0.1% of the
        // expected means.
        let alpha = vec![0.05, 0.025, 0.075, 0.05];
        let n = 150000;
        let rtol = 1e-3;
        let seed = 1317624576693539401;
        check_dirichlet_means(&alpha, n, rtol, seed);
    }

    #[test]
    #[should_panic]
    fn test_dirichlet_invalid_length() {
        Dirichlet::new_with_size(0.5f64, 1).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_dirichlet_invalid_length_slice() {
        Dirichlet::new(&[0.25]).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_dirichlet_invalid_alpha() {
        Dirichlet::new_with_size(0.0f64, 2).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_dirichlet_invalid_alpha_slice() {
        // 0 in alpha must result in a panic.
        Dirichlet::new(&[0.1f64, 0.0f64, 1.5f64]).unwrap();
    }

    #[test]
    fn dirichlet_distributions_can_be_compared() {
        assert_eq!(Dirichlet::new(&[1.0, 2.0]), Dirichlet::new(&[1.0, 2.0]));
    }
}
