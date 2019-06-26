// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
//! The triangular distribution.

use rand::Rng;
use crate::{Distribution, Standard};
use crate::utils::Float;

/// The triangular distribution.
/// 
/// A continuous probability distribution parameterised by a range, and a mode
/// (most likely value) within that range.
///
/// The probability density function is triangular. For a similar distribution
/// with a smooth PDF, see the [`Pert`] distribution.
///
/// # Example
///
/// ```rust
/// use rand_distr::{Triangular, Distribution};
///
/// let d = Triangular::new(0., 5., 2.5).unwrap();
/// let v = d.sample(&mut rand::thread_rng());
/// println!("{} is from a triangular distribution", v);
/// ```
///
/// [`Pert`]: crate::Pert
#[derive(Clone, Copy, Debug)]
pub struct Triangular<N> {
    min: N,
    max: N,
    mode: N,
}

/// Error type returned from [`Triangular::new`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TriangularError {
    /// `max < min` or `min` or `max` is NaN.
    RangeTooSmall,
    /// `mode < min` or `mode > max` or `mode` is NaN.
    ModeRange,
}

impl<N: Float> Triangular<N>
where Standard: Distribution<N>
{
    /// Set up the Triangular distribution with defined `min`, `max` and `mode`.
    #[inline]
    pub fn new(min: N, max: N, mode: N) -> Result<Triangular<N>, TriangularError> {
        if !(max >= min) {
            return Err(TriangularError::RangeTooSmall);
        }
        if !(mode >= min && max >= mode) {
            return Err(TriangularError::ModeRange);
        }
        Ok(Triangular { min, max, mode })
    }
}

impl<N: Float> Distribution<N> for Triangular<N>
where Standard: Distribution<N>
{
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> N {
        let f: N = rng.sample(Standard);
        let diff_mode_min = self.mode - self.min;
        let range = self.max - self.min;
        let f_range = f * range;
        if f_range < diff_mode_min {
            self.min + (f_range * diff_mode_min).sqrt()
        } else {
            self.max - ((range - f_range) * (self.max - self.mode)).sqrt()
        }
    }
}

#[cfg(test)]
mod test {
    use std::f64;
    use rand::{Rng, rngs::mock};
    use super::*;

    #[test]
    fn test_triangular() {
        let mut half_rng = mock::StepRng::new(0x8000_0000_0000_0000, 0);
        assert_eq!(half_rng.gen::<f64>(), 0.5);
        for &(min, max, mode, median) in &[
            (-1., 1., 0., 0.),
            (1., 2., 1., 2. - 0.5f64.sqrt()),
            (5., 25., 25., 5. + 200f64.sqrt()),
            (1e-5, 1e5, 1e-3, 1e5 - 4999999949.5f64.sqrt()),
            (0., 1., 0.9, 0.45f64.sqrt()),
            (-4., -0.5, -2., -4.0 + 3.5f64.sqrt()),
        ] {
            println!("{} {} {} {}", min, max, mode, median);
            let distr = Triangular::new(min, max, mode).unwrap();
            // Test correct value at median:
            assert_eq!(distr.sample(&mut half_rng), median);
        }

        for &(min, max, mode) in &[
            (-1., 1., 2.),
            (-1., 1., -2.),
            (2., 1., 1.),
        ] {
            assert!(Triangular::new(min, max, mode).is_err());
        }
    }
    
    #[test]
    fn value_stability() {
        let rng = crate::test::rng(860);
        let distr = Triangular::new(2., 10., 3.).unwrap();
        let seq = distr.sample_iter(rng).take(5).collect::<Vec<f64>>();
        println!("seq: {:?}", seq);
        let expected = vec![5.74373257511361, 7.890059162791258,
                4.7256280652553455, 2.9474808121184077, 3.058301946314053];
        assert!(seq == expected);
    }
}
