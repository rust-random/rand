// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
//! The PERT distribution.

use rand::Rng;
use crate::{Distribution, Beta, StandardNormal, Exp1, Open01};
use crate::utils::Float;

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

impl<N: Float> Pert<N>
where StandardNormal: Distribution<N>, Exp1: Distribution<N>, Open01: Distribution<N>
{
    /// Set up the PERT distribution with defined `min`, `max` and `mode`.
    ///
    /// This is equivalent to calling `Pert::new_shape` with `shape == 4.0`.
    #[inline]
    pub fn new(min: N, max: N, mode: N) -> Result<Pert<N>, PertError> {
        Pert::new_with_shape(min, max, mode, N::from(4.))
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
        if !(shape >= N::from(0.)) {
            return Err(PertError::ShapeTooSmall);
        }
        
        let range = max - min;
        let mu = (min + max + shape * mode) / (shape + N::from(2.));
        let v = if mu == mode {
            shape * N::from(0.5) + N::from(1.)
        } else {
            (mu - min) * (N::from(2.) * mode - min - max)
                / ((mode - mu) * (max - min))
        };
        let w = v * (max - mu) / (mu - min);
        let beta = Beta::new(v, w).map_err(|_| PertError::RangeTooSmall)?;
        Ok(Pert{ min, range, beta })
    }
}

impl<N: Float> Distribution<N> for Pert<N>
where StandardNormal: Distribution<N>, Exp1: Distribution<N>, Open01: Distribution<N>
{
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> N {
        self.beta.sample(rng) * self.range + self.min
    }
}

#[cfg(test)]
mod test {
    use std::f64;
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
        let distr = Pert::new(2., 10., 3.).unwrap();    // mean = 4, var = 12/7
        let seq = distr.sample_iter(rng).take(5).collect::<Vec<f64>>();
        println!("seq: {:?}", seq);
        let expected = vec![4.631484136029422, 3.307201472321789,
                3.29995019556348, 3.66835483991721, 3.514246139933899];
        assert!(seq == expected);
    }
}
