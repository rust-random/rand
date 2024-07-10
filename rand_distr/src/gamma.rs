// Copyright 2018 Developers of the Rand project.
// Copyright 2013 The Rust Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The Gamma and derived distributions.

// We use the variable names from the published reference, therefore this
// warning is not helpful.
#![allow(clippy::many_single_char_names)]

use self::ChiSquaredRepr::*;
use self::GammaRepr::*;

use crate::normal::StandardNormal;
use crate::{Distribution, Exp, Exp1, Open01};
use core::fmt;
use num_traits::Float;
use rand::Rng;
#[cfg(feature = "serde1")]
use serde::{Deserialize, Serialize};

/// The [Gamma distribution](https://en.wikipedia.org/wiki/Gamma_distribution) `Gamma(k, θ)`.
///
/// The Gamma distribution is a continuous probability distribution
/// with shape parameter `k > 0` (number of events) and
/// scale parameter `θ > 0` (mean waiting time between events).
/// It describes the time until `k` events occur in a Poisson
/// process with rate `1/θ`. It is the generalization of the
/// [`Exponential`](crate::Exp) distribution.
///
/// # Density function
///
/// `f(x) =  x^(k - 1) * exp(-x / θ) / (Γ(k) * θ^k)` for `x > 0`,
/// where `Γ` is the [gamma function](https://en.wikipedia.org/wiki/Gamma_function).
///
/// # Plot
///
/// The following plot illustrates the Gamma distribution with
/// various values of `k` and `θ`.
/// Curves with `θ = 1` are more saturated, while corresponding
/// curves with `θ = 2` have a lighter color.
///
/// ![Gamma distribution](https://raw.githubusercontent.com/rust-random/charts/main/charts/gamma.svg)
///
/// # Example
///
/// ```
/// use rand_distr::{Distribution, Gamma};
///
/// let gamma = Gamma::new(2.0, 5.0).unwrap();
/// let v = gamma.sample(&mut rand::thread_rng());
/// println!("{} is from a Gamma(2, 5) distribution", v);
/// ```
///
/// # Notes
///
/// The algorithm used is that described by Marsaglia & Tsang 2000[^1],
/// falling back to directly sampling from an Exponential for `shape
/// == 1`, and using the boosting technique described in that paper for
/// `shape < 1`.
///
/// [^1]: George Marsaglia and Wai Wan Tsang. 2000. "A Simple Method for
///       Generating Gamma Variables" *ACM Trans. Math. Softw.* 26, 3
///       (September 2000), 363-372.
///       DOI:[10.1145/358407.358414](https://doi.acm.org/10.1145/358407.358414)
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
pub struct Gamma<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    repr: GammaRepr<F>,
}

/// Error type returned from `Gamma::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// `shape <= 0` or `nan`.
    ShapeTooSmall,
    /// `scale <= 0` or `nan`.
    ScaleTooSmall,
    /// `1 / scale == 0`.
    ScaleTooLarge,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::ShapeTooSmall => "shape is not positive in gamma distribution",
            Error::ScaleTooSmall => "scale is not positive in gamma distribution",
            Error::ScaleTooLarge => "scale is infinity in gamma distribution",
        })
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}

#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
enum GammaRepr<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    Large(GammaLargeShape<F>),
    One(Exp<F>),
    Small(GammaSmallShape<F>),
}

// These two helpers could be made public, but saving the
// match-on-Gamma-enum branch from using them directly (e.g. if one
// knows that the shape is always > 1) doesn't appear to be much
// faster.

/// Gamma distribution where the shape parameter is less than 1.
///
/// Note, samples from this require a compulsory floating-point `pow`
/// call, which makes it significantly slower than sampling from a
/// gamma distribution where the shape parameter is greater than or
/// equal to 1.
///
/// See `Gamma` for sampling from a Gamma distribution with general
/// shape parameters.
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
struct GammaSmallShape<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Open01: Distribution<F>,
{
    inv_shape: F,
    large_shape: GammaLargeShape<F>,
}

/// Gamma distribution where the shape parameter is larger than 1.
///
/// See `Gamma` for sampling from a Gamma distribution with general
/// shape parameters.
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
struct GammaLargeShape<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Open01: Distribution<F>,
{
    scale: F,
    c: F,
    d: F,
}

impl<F> Gamma<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    /// Construct an object representing the `Gamma(shape, scale)`
    /// distribution.
    #[inline]
    pub fn new(shape: F, scale: F) -> Result<Gamma<F>, Error> {
        if !(shape > F::zero()) {
            return Err(Error::ShapeTooSmall);
        }
        if !(scale > F::zero()) {
            return Err(Error::ScaleTooSmall);
        }

        let repr = if shape == F::one() {
            One(Exp::new(F::one() / scale).map_err(|_| Error::ScaleTooLarge)?)
        } else if shape < F::one() {
            Small(GammaSmallShape::new_raw(shape, scale))
        } else {
            Large(GammaLargeShape::new_raw(shape, scale))
        };
        Ok(Gamma { repr })
    }
}

impl<F> GammaSmallShape<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Open01: Distribution<F>,
{
    fn new_raw(shape: F, scale: F) -> GammaSmallShape<F> {
        GammaSmallShape {
            inv_shape: F::one() / shape,
            large_shape: GammaLargeShape::new_raw(shape + F::one(), scale),
        }
    }
}

impl<F> GammaLargeShape<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Open01: Distribution<F>,
{
    fn new_raw(shape: F, scale: F) -> GammaLargeShape<F> {
        let d = shape - F::from(1. / 3.).unwrap();
        GammaLargeShape {
            scale,
            c: F::one() / (F::from(9.).unwrap() * d).sqrt(),
            d,
        }
    }
}

impl<F> Distribution<F> for Gamma<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> F {
        match self.repr {
            Small(ref g) => g.sample(rng),
            One(ref g) => g.sample(rng),
            Large(ref g) => g.sample(rng),
        }
    }
}
impl<F> Distribution<F> for GammaSmallShape<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Open01: Distribution<F>,
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> F {
        let u: F = rng.sample(Open01);

        self.large_shape.sample(rng) * u.powf(self.inv_shape)
    }
}
impl<F> Distribution<F> for GammaLargeShape<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Open01: Distribution<F>,
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> F {
        // Marsaglia & Tsang method, 2000
        loop {
            let x: F = rng.sample(StandardNormal);
            let v_cbrt = F::one() + self.c * x;
            if v_cbrt <= F::zero() {
                // a^3 <= 0 iff a <= 0
                continue;
            }

            let v = v_cbrt * v_cbrt * v_cbrt;
            let u: F = rng.sample(Open01);

            let x_sqr = x * x;
            if u < F::one() - F::from(0.0331).unwrap() * x_sqr * x_sqr
                || u.ln() < F::from(0.5).unwrap() * x_sqr + self.d * (F::one() - v + v.ln())
            {
                return self.d * v * self.scale;
            }
        }
    }
}

/// The [chi-squared distribution](https://en.wikipedia.org/wiki/Chi-squared_distribution) `χ²(k)`.
///
/// The chi-squared distribution is a continuous probability
/// distribution with parameter `k > 0` degrees of freedom.
///
/// For `k > 0` integral, this distribution is the sum of the squares
/// of `k` independent standard normal random variables. For other
/// `k`, this uses the equivalent characterisation
/// `χ²(k) = Gamma(k/2, 2)`.
///
/// # Plot
///
/// The plot shows the chi-squared distribution with various degrees
/// of freedom.
///
/// ![Chi-squared distribution](https://raw.githubusercontent.com/rust-random/charts/main/charts/chi_squared.svg)
///
/// # Example
///
/// ```
/// use rand_distr::{ChiSquared, Distribution};
///
/// let chi = ChiSquared::new(11.0).unwrap();
/// let v = chi.sample(&mut rand::thread_rng());
/// println!("{} is from a χ²(11) distribution", v)
/// ```
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
pub struct ChiSquared<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    repr: ChiSquaredRepr<F>,
}

/// Error type returned from `ChiSquared::new` and `StudentT::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
pub enum ChiSquaredError {
    /// `0.5 * k <= 0` or `nan`.
    DoFTooSmall,
}

impl fmt::Display for ChiSquaredError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            ChiSquaredError::DoFTooSmall => {
                "degrees-of-freedom k is not positive in chi-squared distribution"
            }
        })
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ChiSquaredError {}

#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde1", derive(Serialize, Deserialize))]
enum ChiSquaredRepr<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    // k == 1, Gamma(alpha, ..) is particularly slow for alpha < 1,
    // e.g. when alpha = 1/2 as it would be for this case, so special-
    // casing and using the definition of N(0,1)^2 is faster.
    DoFExactlyOne,
    DoFAnythingElse(Gamma<F>),
}

impl<F> ChiSquared<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    /// Create a new chi-squared distribution with degrees-of-freedom
    /// `k`.
    pub fn new(k: F) -> Result<ChiSquared<F>, ChiSquaredError> {
        let repr = if k == F::one() {
            DoFExactlyOne
        } else {
            if !(F::from(0.5).unwrap() * k > F::zero()) {
                return Err(ChiSquaredError::DoFTooSmall);
            }
            DoFAnythingElse(Gamma::new(F::from(0.5).unwrap() * k, F::from(2.0).unwrap()).unwrap())
        };
        Ok(ChiSquared { repr })
    }
}
impl<F> Distribution<F> for ChiSquared<F>
where
    F: Float,
    StandardNormal: Distribution<F>,
    Exp1: Distribution<F>,
    Open01: Distribution<F>,
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> F {
        match self.repr {
            DoFExactlyOne => {
                // k == 1 => N(0,1)^2
                let norm: F = rng.sample(StandardNormal);
                norm * norm
            }
            DoFAnythingElse(ref g) => g.sample(rng),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_chi_squared_one() {
        let chi = ChiSquared::new(1.0).unwrap();
        let mut rng = crate::test::rng(201);
        for _ in 0..1000 {
            chi.sample(&mut rng);
        }
    }
    #[test]
    fn test_chi_squared_small() {
        let chi = ChiSquared::new(0.5).unwrap();
        let mut rng = crate::test::rng(202);
        for _ in 0..1000 {
            chi.sample(&mut rng);
        }
    }
    #[test]
    fn test_chi_squared_large() {
        let chi = ChiSquared::new(30.0).unwrap();
        let mut rng = crate::test::rng(203);
        for _ in 0..1000 {
            chi.sample(&mut rng);
        }
    }
    #[test]
    #[should_panic]
    fn test_chi_squared_invalid_dof() {
        ChiSquared::new(-1.0).unwrap();
    }

    #[test]
    fn gamma_distributions_can_be_compared() {
        assert_eq!(Gamma::new(1.0, 2.0), Gamma::new(1.0, 2.0));
    }

    #[test]
    fn chi_squared_distributions_can_be_compared() {
        assert_eq!(ChiSquared::new(1.0), ChiSquared::new(1.0));
    }
}
