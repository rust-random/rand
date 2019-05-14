// Copyright 2018 Developers of the Rand project.
// Copyright 2013 The Rust Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The normal and derived distributions.

use rand::Rng;
use crate::{ziggurat_tables, Distribution, Open01};
use crate::utils::{ziggurat, Float};

/// Samples floating-point numbers according to the normal distribution
/// `N(0, 1)` (a.k.a. a standard normal, or Gaussian). This is equivalent to
/// `Normal::new(0.0, 1.0)` but faster.
///
/// See `Normal` for the general normal distribution.
///
/// Implemented via the ZIGNOR variant[^1] of the Ziggurat method.
///
/// [^1]: Jurgen A. Doornik (2005). [*An Improved Ziggurat Method to
///       Generate Normal Random Samples*](
///       https://www.doornik.com/research/ziggurat.pdf).
///       Nuffield College, Oxford
///
/// # Example
/// ```
/// use rand::prelude::*;
/// use rand_distr::StandardNormal;
///
/// let val: f64 = thread_rng().sample(StandardNormal);
/// println!("{}", val);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct StandardNormal;

impl Distribution<f32> for StandardNormal {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> f32 {
        // TODO: use optimal 32-bit implementation
        let x: f64 = self.sample(rng);
        x as f32
    }
}

impl Distribution<f64> for StandardNormal {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> f64 {
        #[inline]
        fn pdf(x: f64) -> f64 {
            (-x*x/2.0).exp()
        }
        #[inline]
        fn zero_case<R: Rng + ?Sized>(rng: &mut R, u: f64) -> f64 {
            // compute a random number in the tail by hand

            // strange initial conditions, because the loop is not
            // do-while, so the condition should be true on the first
            // run, they get overwritten anyway (0 < 1, so these are
            // good).
            let mut x = 1.0f64;
            let mut y = 0.0f64;

            while -2.0 * y < x * x {
                let x_: f64 = rng.sample(Open01);
                let y_: f64 = rng.sample(Open01);

                x = x_.ln() / ziggurat_tables::ZIG_NORM_R;
                y = y_.ln();
            }

            if u < 0.0 { x - ziggurat_tables::ZIG_NORM_R } else { ziggurat_tables::ZIG_NORM_R - x }
        }

        ziggurat(rng, true, // this is symmetric
                 &ziggurat_tables::ZIG_NORM_X,
                 &ziggurat_tables::ZIG_NORM_F,
                 pdf, zero_case)
    }
}

/// The normal distribution `N(mean, std_dev**2)`.
///
/// This uses the ZIGNOR variant of the Ziggurat method, see [`StandardNormal`]
/// for more details.
/// 
/// Note that [`StandardNormal`] is an optimised implementation for mean 0, and
/// standard deviation 1.
///
/// # Example
///
/// ```
/// use rand_distr::{Normal, Distribution};
///
/// // mean 2, standard deviation 3
/// let normal = Normal::new(2.0, 3.0).unwrap();
/// let v = normal.sample(&mut rand::thread_rng());
/// println!("{} is from a N(2, 9) distribution", v)
/// ```
///
/// [`StandardNormal`]: crate::StandardNormal
#[derive(Clone, Copy, Debug)]
pub struct Normal<N> {
    mean: N,
    std_dev: N,
}

/// Error type returned from `Normal::new` and `LogNormal::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// `std_dev < 0` or `nan`.
    StdDevTooSmall,
}

impl<N: Float> Normal<N>
where StandardNormal: Distribution<N>
{
    /// Construct a new `Normal` distribution with the given mean and
    /// standard deviation.
    #[inline]
    pub fn new(mean: N, std_dev: N) -> Result<Normal<N>, Error> {
        if !(std_dev >= N::from(0.0)) {
            return Err(Error::StdDevTooSmall);
        }
        Ok(Normal {
            mean,
            std_dev
        })
    }
}

impl<N: Float> Distribution<N> for Normal<N>
where StandardNormal: Distribution<N>
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> N {
        let n: N = rng.sample(StandardNormal);
        self.mean + self.std_dev * n
    }
}


/// The log-normal distribution `ln N(mean, std_dev**2)`.
///
/// If `X` is log-normal distributed, then `ln(X)` is `N(mean, std_dev**2)`
/// distributed.
///
/// # Example
///
/// ```
/// use rand_distr::{LogNormal, Distribution};
///
/// // mean 2, standard deviation 3
/// let log_normal = LogNormal::new(2.0, 3.0).unwrap();
/// let v = log_normal.sample(&mut rand::thread_rng());
/// println!("{} is from an ln N(2, 9) distribution", v)
/// ```
#[derive(Clone, Copy, Debug)]
pub struct LogNormal<N> {
    norm: Normal<N>
}

impl<N: Float> LogNormal<N>
where StandardNormal: Distribution<N>
{
    /// Construct a new `LogNormal` distribution with the given mean
    /// and standard deviation of the logarithm of the distribution.
    #[inline]
    pub fn new(mean: N, std_dev: N) -> Result<LogNormal<N>, Error> {
        if !(std_dev >= N::from(0.0)) {
            return Err(Error::StdDevTooSmall);
        }
        Ok(LogNormal { norm: Normal::new(mean, std_dev).unwrap() })
    }
}

impl<N: Float> Distribution<N> for LogNormal<N>
where StandardNormal: Distribution<N>
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> N {
        self.norm.sample(rng).exp()
    }
}

#[cfg(test)]
mod tests {
    use crate::Distribution;
    use super::{Normal, LogNormal};

    #[test]
    fn test_normal() {
        let norm = Normal::new(10.0, 10.0).unwrap();
        let mut rng = crate::test::rng(210);
        for _ in 0..1000 {
            norm.sample(&mut rng);
        }
    }
    #[test]
    #[should_panic]
    fn test_normal_invalid_sd() {
        Normal::new(10.0, -1.0).unwrap();
    }


    #[test]
    fn test_log_normal() {
        let lnorm = LogNormal::new(10.0, 10.0).unwrap();
        let mut rng = crate::test::rng(211);
        for _ in 0..1000 {
            lnorm.sample(&mut rng);
        }
    }
    #[test]
    #[should_panic]
    fn test_log_normal_invalid_sd() {
        LogNormal::new(10.0, -1.0).unwrap();
    }
}
