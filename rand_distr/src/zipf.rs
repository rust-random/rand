// Copyright 2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The Zipf distribution.

use num_traits::Float;
use crate::{Distribution, Standard};
use rand::{Rng, distributions::OpenClosed01};
use core::fmt;

/// Samples floating-point numbers according to the Zipf distribution.
///
/// The Zipf distribution (also known as the zeta distribution) is a continuous
/// probability distribution that satisfies Zipf’s law: the frequency of an item
/// is inversely proportional to its rank in a frequency table.
///
/// # Example
/// ```
/// use rand::prelude::*;
/// use rand_distr::Zipf;
///
/// let val: f64 = thread_rng().sample(Zipf::new(1.5).unwrap());
/// println!("{}", val);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Zipf<F>
where F: Float, Standard: Distribution<F>, OpenClosed01: Distribution<F>
{
    a_minus_1: F,
    b: F,
}

/// Error type returned from `Zipf::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// `a <= 1` or `nan`.
    ATooSmall,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::ATooSmall => "a <= 0 or is NaN in Zipf distribution",
        })
    }
}

#[cfg(feature = "std")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "std")))]
impl std::error::Error for Error {}

impl<F> Zipf<F>
where F: Float, Standard: Distribution<F>, OpenClosed01: Distribution<F>
{
    /// Construct a new `Zipf` distribution with given `a` parameter.
    pub fn new(a: F) -> Result<Zipf<F>, Error> {
        if !(a > F::one()) {
            return Err(Error::ATooSmall);
        }
        let a_minus_1 = a - F::one();
        let two = F::one() + F::one();
        Ok(Zipf {
            a_minus_1,
            b: two.powf(a_minus_1),
        })
    }
}

impl<F> Distribution<F> for Zipf<F>
where F: Float, Standard: Distribution<F>, OpenClosed01: Distribution<F>
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> F {
        // This is based on the numpy implementation.
        loop {
            let u = rng.sample(OpenClosed01);
            let v = rng.sample(Standard);
            let x = u.powf(-F::one() / self.a_minus_1).floor();

            if x < F::one() {
                continue;
            }

            let t = (F::one() + F::one() / x).powf(self.a_minus_1);
            if v * x * (t - F::one()) / (self.b - F::one()) <= t / self.b {
                return x;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic]
    fn invalid() {
        Zipf::new(1.).unwrap();
    }

    #[test]
    #[should_panic]
    fn nan() {
        Zipf::new(core::f64::NAN).unwrap();
    }

    #[test]
    fn sample() {
        let a = 2.0;
        let d = Zipf::new(a).unwrap();
        let mut rng = crate::test::rng(1);
        for _ in 0..1000 {
            let r = d.sample(&mut rng);
            assert!(r >= 1.);
        }
    }

    #[test]
    fn value_stability() {
        fn test_samples<F: Float + core::fmt::Debug, D: Distribution<F>>(
            distr: D, zero: F, expected: &[F],
        ) {
            let mut rng = crate::test::rng(213);
            let mut buf = [zero; 4];
            for x in &mut buf {
                *x = rng.sample(&distr);
            }
            assert_eq!(buf, expected);
        }

        test_samples(Zipf::new(1.5).unwrap(), 0f32, &[
            605.0, 1.0, 8.0, 15.0,
        ]);
        test_samples(Zipf::new(2.0).unwrap(), 0f64, &[
            1.0, 2.0, 4.0, 1.0,
        ]);
    }
}
