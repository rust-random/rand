// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
//! The PERT distribution.

use num_traits::Float;
use crate::{Beta, Distribution, Exp1, Open01, StandardNormal};
use rand::Rng;
use core::fmt;

/// The PERT distribution.
///
/// Similar to the [`Triangular`] distribution, the PERT distribution is
/// parameterised by a range and a mode within that range. Unlike the
/// [`Triangular`] distribution, the probability density function of the PERT
/// distribution is smooth, with a configurable weighting around the mode.
///
/// # Example
///
/// ```rust
/// use rand_distr::{Pert, Distribution};
///
/// let d = Pert::new(0., 5., 2.5).unwrap();
/// let v = d.sample(&mut rand::thread_rng());
/// println!("{} is from a PERT distribution", v);
/// ```
///
/// [`Triangular`]: crate::Triangular
#[derive(Clone, Copy, Debug)]
pub struct Pert<N> {
    min: N,
    range: N,
    beta: Beta<N>,
}

/// Error type returned from [`Pert`] constructors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PertError {
    /// `max < min` or `min` or `max` is NaN.
    RangeTooSmall,
    /// `mode < min` or `mode > max` or `mode` is NaN.
    ModeRange,
    /// `shape < 0` or `shape` is NaN
    ShapeTooSmall,
}

impl fmt::Display for PertError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            PertError::RangeTooSmall => "requirement min < max is not met in PERT distribution",
            PertError::ModeRange => "mode is outside [min, max] in PERT distribution",
            PertError::ShapeTooSmall => "shape < 0 or is NaN in PERT distribution",
        })
    }
}

#[cfg(feature = "std")]
impl std::error::Error for PertError {}

impl<N: Float> Pert<N>
where
    StandardNormal: Distribution<N>,
    Exp1: Distribution<N>,
    Open01: Distribution<N>,
{
    /// Set up the PERT distribution with defined `min`, `max` and `mode`.
    ///
    /// This is equivalent to calling `Pert::new_shape` with `shape == 4.0`.
    #[inline]
    pub fn new(min: N, max: N, mode: N) -> Result<Pert<N>, PertError> {
        Pert::new_with_shape(min, max, mode, N::from(4.).unwrap())
    }

    /// Set up the PERT distribution with defined `min`, `max`, `mode` and
    /// `shape`.
    pub fn new_with_shape(min: N, max: N, mode: N, shape: N) -> Result<Pert<N>, PertError> {
        if !(max > min) {
            return Err(PertError::RangeTooSmall);
        }
        if !(mode >= min && max >= mode) {
            return Err(PertError::ModeRange);
        }
        if !(shape >= N::from(0.).unwrap()) {
            return Err(PertError::ShapeTooSmall);
        }

        let range = max - min;
        let mu = (min + max + shape * mode) / (shape + N::from(2.).unwrap());
        let v = if mu == mode {
            shape * N::from(0.5).unwrap() + N::from(1.).unwrap()
        } else {
            (mu - min) * (N::from(2.).unwrap() * mode - min - max) / ((mode - mu) * (max - min))
        };
        let w = v * (max - mu) / (mu - min);
        let beta = Beta::new(v, w).map_err(|_| PertError::RangeTooSmall)?;
        Ok(Pert { min, range, beta })
    }
}

impl<N: Float> Distribution<N> for Pert<N>
where
    StandardNormal: Distribution<N>,
    Exp1: Distribution<N>,
    Open01: Distribution<N>,
{
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> N {
        self.beta.sample(rng) * self.range + self.min
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_pert() {
        for &(min, max, mode) in &[
            (-1., 1., 0.),
            (1., 2., 1.),
            (5., 25., 25.),
        ] {
            let _distr = Pert::new(min, max, mode).unwrap();
            // TODO: test correctness
        }

        for &(min, max, mode) in &[
            (-1., 1., 2.),
            (-1., 1., -2.),
            (2., 1., 1.),
        ] {
            assert!(Pert::new(min, max, mode).is_err());
        }
    }

    #[test]
    fn value_stability() {
        let rng = crate::test::rng(860);
        let distr = Pert::new(2., 10., 3.).unwrap(); // mean = 4, var = 12/7
        let mut seq = distr.sample_iter(rng);
        assert_eq!(seq.next(), Some(4.631484136029422f64));
        assert_eq!(seq.next(), Some(3.307201472321789f64));
        assert_eq!(seq.next(), Some(3.29995019556348f64));
        assert_eq!(seq.next(), Some(3.66835483991721f64));
        assert_eq!(seq.next(), Some(3.514246139933899f64));
    }
}
