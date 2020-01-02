// Copyright 2018 Developers of the Rand project.
// Copyright 2013 The Rust Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The normal and derived distributions.

use crate::utils::{ziggurat, Float};
use crate::{ziggurat_tables, Distribution, Open01};
use rand::Rng;
use std::{error, fmt};

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
            (-x * x / 2.0).exp()
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

            if u < 0.0 {
                x - ziggurat_tables::ZIG_NORM_R
            } else {
                ziggurat_tables::ZIG_NORM_R - x
            }
        }

        ziggurat(
            rng,
            true, // this is symmetric
            &ziggurat_tables::ZIG_NORM_X,
            &ziggurat_tables::ZIG_NORM_F,
            pdf,
            zero_case,
        )
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

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::StdDevTooSmall => "std_dev < 0 or is NaN in normal distribution",
        })
    }
}

impl error::Error for Error {}

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
        Ok(Normal { mean, std_dev })
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
    norm: Normal<N>,
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
        Ok(LogNormal {
            norm: Normal::new(mean, std_dev).unwrap(),
        })
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
    use super::*;

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

        test_samples(StandardNormal, 0f32, &[
            -0.11844189,
            0.781378,
            0.06563994,
            -1.1932899,
        ]);
        test_samples(StandardNormal, 0f64, &[
            -0.11844188827977231,
            0.7813779637772346,
            0.06563993969580051,
            -1.1932899004186373,
        ]);

        test_samples(Normal::new(0.0, 1.0).unwrap(), 0f32, &[
            -0.11844189,
            0.781378,
            0.06563994,
            -1.1932899,
        ]);
        test_samples(Normal::new(2.0, 0.5).unwrap(), 0f64, &[
            1.940779055860114,
            2.3906889818886174,
            2.0328199698479,
            1.4033550497906813,
        ]);

        test_samples(LogNormal::new(0.0, 1.0).unwrap(), 0f32, &[
            0.88830346, 2.1844804, 1.0678421, 0.30322206,
        ]);
        test_samples(LogNormal::new(2.0, 0.5).unwrap(), 0f64, &[
            6.964174338639032,
            10.921015733601452,
            7.6355881556915906,
            4.068828213584092,
        ]);
    }
}
