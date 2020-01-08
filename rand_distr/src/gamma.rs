// Copyright 2018 Developers of the Rand project.
// Copyright 2013 The Rust Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The Gamma and derived distributions.

use self::ChiSquaredRepr::*;
use self::GammaRepr::*;

use crate::normal::StandardNormal;
use crate::utils::Float;
use crate::{Distribution, Exp, Exp1, Open01};
use rand::Rng;
use std::{error, fmt};

/// The Gamma distribution `Gamma(shape, scale)` distribution.
///
/// The density function of this distribution is
///
/// ```text
/// f(x) =  x^(k - 1) * exp(-x / θ) / (Γ(k) * θ^k)
/// ```
///
/// where `Γ` is the Gamma function, `k` is the shape and `θ` is the
/// scale and both `k` and `θ` are strictly positive.
///
/// The algorithm used is that described by Marsaglia & Tsang 2000[^1],
/// falling back to directly sampling from an Exponential for `shape
/// == 1`, and using the boosting technique described in that paper for
/// `shape < 1`.
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
/// [^1]: George Marsaglia and Wai Wan Tsang. 2000. "A Simple Method for
///       Generating Gamma Variables" *ACM Trans. Math. Softw.* 26, 3
///       (September 2000), 363-372.
///       DOI:[10.1145/358407.358414](https://doi.acm.org/10.1145/358407.358414)
#[derive(Clone, Copy, Debug)]
pub struct Gamma<N> {
    repr: GammaRepr<N>,
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

impl error::Error for Error {}

#[derive(Clone, Copy, Debug)]
enum GammaRepr<N> {
    Large(GammaLargeShape<N>),
    One(Exp<N>),
    Small(GammaSmallShape<N>),
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
#[derive(Clone, Copy, Debug)]
struct GammaSmallShape<N> {
    inv_shape: N,
    large_shape: GammaLargeShape<N>,
}

/// Gamma distribution where the shape parameter is larger than 1.
///
/// See `Gamma` for sampling from a Gamma distribution with general
/// shape parameters.
#[derive(Clone, Copy, Debug)]
struct GammaLargeShape<N> {
    scale: N,
    c: N,
    d: N,
}

impl<N: Float> Gamma<N>
where
    StandardNormal: Distribution<N>,
    Exp1: Distribution<N>,
    Open01: Distribution<N>,
{
    /// Construct an object representing the `Gamma(shape, scale)`
    /// distribution.
    #[inline]
    pub fn new(shape: N, scale: N) -> Result<Gamma<N>, Error> {
        if !(shape > N::from(0.0)) {
            return Err(Error::ShapeTooSmall);
        }
        if !(scale > N::from(0.0)) {
            return Err(Error::ScaleTooSmall);
        }

        let repr = if shape == N::from(1.0) {
            One(Exp::new(N::from(1.0) / scale).map_err(|_| Error::ScaleTooLarge)?)
        } else if shape < N::from(1.0) {
            Small(GammaSmallShape::new_raw(shape, scale))
        } else {
            Large(GammaLargeShape::new_raw(shape, scale))
        };
        Ok(Gamma { repr })
    }
}

impl<N: Float> GammaSmallShape<N>
where
    StandardNormal: Distribution<N>,
    Open01: Distribution<N>,
{
    fn new_raw(shape: N, scale: N) -> GammaSmallShape<N> {
        GammaSmallShape {
            inv_shape: N::from(1.0) / shape,
            large_shape: GammaLargeShape::new_raw(shape + N::from(1.0), scale),
        }
    }
}

impl<N: Float> GammaLargeShape<N>
where
    StandardNormal: Distribution<N>,
    Open01: Distribution<N>,
{
    fn new_raw(shape: N, scale: N) -> GammaLargeShape<N> {
        let d = shape - N::from(1. / 3.);
        GammaLargeShape {
            scale,
            c: N::from(1.0) / (N::from(9.) * d).sqrt(),
            d,
        }
    }
}

impl<N: Float> Distribution<N> for Gamma<N>
where
    StandardNormal: Distribution<N>,
    Exp1: Distribution<N>,
    Open01: Distribution<N>,
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> N {
        match self.repr {
            Small(ref g) => g.sample(rng),
            One(ref g) => g.sample(rng),
            Large(ref g) => g.sample(rng),
        }
    }
}
impl<N: Float> Distribution<N> for GammaSmallShape<N>
where
    StandardNormal: Distribution<N>,
    Open01: Distribution<N>,
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> N {
        let u: N = rng.sample(Open01);

        self.large_shape.sample(rng) * u.powf(self.inv_shape)
    }
}
impl<N: Float> Distribution<N> for GammaLargeShape<N>
where
    StandardNormal: Distribution<N>,
    Open01: Distribution<N>,
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> N {
        // Marsaglia & Tsang method, 2000
        loop {
            let x: N = rng.sample(StandardNormal);
            let v_cbrt = N::from(1.0) + self.c * x;
            if v_cbrt <= N::from(0.0) {
                // a^3 <= 0 iff a <= 0
                continue;
            }

            let v = v_cbrt * v_cbrt * v_cbrt;
            let u: N = rng.sample(Open01);

            let x_sqr = x * x;
            if u < N::from(1.0) - N::from(0.0331) * x_sqr * x_sqr
                || u.ln() < N::from(0.5) * x_sqr + self.d * (N::from(1.0) - v + v.ln())
            {
                return self.d * v * self.scale;
            }
        }
    }
}

/// The chi-squared distribution `χ²(k)`, where `k` is the degrees of
/// freedom.
///
/// For `k > 0` integral, this distribution is the sum of the squares
/// of `k` independent standard normal random variables. For other
/// `k`, this uses the equivalent characterisation
/// `χ²(k) = Gamma(k/2, 2)`.
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
#[derive(Clone, Copy, Debug)]
pub struct ChiSquared<N> {
    repr: ChiSquaredRepr<N>,
}

/// Error type returned from `ChiSquared::new` and `StudentT::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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

impl error::Error for ChiSquaredError {}

#[derive(Clone, Copy, Debug)]
enum ChiSquaredRepr<N> {
    // k == 1, Gamma(alpha, ..) is particularly slow for alpha < 1,
    // e.g. when alpha = 1/2 as it would be for this case, so special-
    // casing and using the definition of N(0,1)^2 is faster.
    DoFExactlyOne,
    DoFAnythingElse(Gamma<N>),
}

impl<N: Float> ChiSquared<N>
where
    StandardNormal: Distribution<N>,
    Exp1: Distribution<N>,
    Open01: Distribution<N>,
{
    /// Create a new chi-squared distribution with degrees-of-freedom
    /// `k`.
    pub fn new(k: N) -> Result<ChiSquared<N>, ChiSquaredError> {
        let repr = if k == N::from(1.0) {
            DoFExactlyOne
        } else {
            if !(N::from(0.5) * k > N::from(0.0)) {
                return Err(ChiSquaredError::DoFTooSmall);
            }
            DoFAnythingElse(Gamma::new(N::from(0.5) * k, N::from(2.0)).unwrap())
        };
        Ok(ChiSquared { repr })
    }
}
impl<N: Float> Distribution<N> for ChiSquared<N>
where
    StandardNormal: Distribution<N>,
    Exp1: Distribution<N>,
    Open01: Distribution<N>,
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> N {
        match self.repr {
            DoFExactlyOne => {
                // k == 1 => N(0,1)^2
                let norm: N = rng.sample(StandardNormal);
                norm * norm
            }
            DoFAnythingElse(ref g) => g.sample(rng),
        }
    }
}

/// The Fisher F distribution `F(m, n)`.
///
/// This distribution is equivalent to the ratio of two normalised
/// chi-squared distributions, that is, `F(m,n) = (χ²(m)/m) /
/// (χ²(n)/n)`.
///
/// # Example
///
/// ```
/// use rand_distr::{FisherF, Distribution};
///
/// let f = FisherF::new(2.0, 32.0).unwrap();
/// let v = f.sample(&mut rand::thread_rng());
/// println!("{} is from an F(2, 32) distribution", v)
/// ```
#[derive(Clone, Copy, Debug)]
pub struct FisherF<N> {
    numer: ChiSquared<N>,
    denom: ChiSquared<N>,
    // denom_dof / numer_dof so that this can just be a straight
    // multiplication, rather than a division.
    dof_ratio: N,
}

/// Error type returned from `FisherF::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FisherFError {
    /// `m <= 0` or `nan`.
    MTooSmall,
    /// `n <= 0` or `nan`.
    NTooSmall,
}

impl fmt::Display for FisherFError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            FisherFError::MTooSmall => "m is not positive in Fisher F distribution",
            FisherFError::NTooSmall => "n is not positive in Fisher F distribution",
        })
    }
}

impl error::Error for FisherFError {}

impl<N: Float> FisherF<N>
where
    StandardNormal: Distribution<N>,
    Exp1: Distribution<N>,
    Open01: Distribution<N>,
{
    /// Create a new `FisherF` distribution, with the given parameter.
    pub fn new(m: N, n: N) -> Result<FisherF<N>, FisherFError> {
        if !(m > N::from(0.0)) {
            return Err(FisherFError::MTooSmall);
        }
        if !(n > N::from(0.0)) {
            return Err(FisherFError::NTooSmall);
        }

        Ok(FisherF {
            numer: ChiSquared::new(m).unwrap(),
            denom: ChiSquared::new(n).unwrap(),
            dof_ratio: n / m,
        })
    }
}
impl<N: Float> Distribution<N> for FisherF<N>
where
    StandardNormal: Distribution<N>,
    Exp1: Distribution<N>,
    Open01: Distribution<N>,
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> N {
        self.numer.sample(rng) / self.denom.sample(rng) * self.dof_ratio
    }
}

/// The Student t distribution, `t(nu)`, where `nu` is the degrees of
/// freedom.
///
/// # Example
///
/// ```
/// use rand_distr::{StudentT, Distribution};
///
/// let t = StudentT::new(11.0).unwrap();
/// let v = t.sample(&mut rand::thread_rng());
/// println!("{} is from a t(11) distribution", v)
/// ```
#[derive(Clone, Copy, Debug)]
pub struct StudentT<N> {
    chi: ChiSquared<N>,
    dof: N,
}

impl<N: Float> StudentT<N>
where
    StandardNormal: Distribution<N>,
    Exp1: Distribution<N>,
    Open01: Distribution<N>,
{
    /// Create a new Student t distribution with `n` degrees of
    /// freedom.
    pub fn new(n: N) -> Result<StudentT<N>, ChiSquaredError> {
        Ok(StudentT {
            chi: ChiSquared::new(n)?,
            dof: n,
        })
    }
}
impl<N: Float> Distribution<N> for StudentT<N>
where
    StandardNormal: Distribution<N>,
    Exp1: Distribution<N>,
    Open01: Distribution<N>,
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> N {
        let norm: N = rng.sample(StandardNormal);
        norm * (self.dof / self.chi.sample(rng)).sqrt()
    }
}

/// The Beta distribution with shape parameters `alpha` and `beta`.
///
/// # Example
///
/// ```
/// use rand_distr::{Distribution, Beta};
///
/// let beta = Beta::new(2.0, 5.0).unwrap();
/// let v = beta.sample(&mut rand::thread_rng());
/// println!("{} is from a Beta(2, 5) distribution", v);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct Beta<N> {
    gamma_a: Gamma<N>,
    gamma_b: Gamma<N>,
}

/// Error type returned from `Beta::new`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BetaError {
    /// `alpha <= 0` or `nan`.
    AlphaTooSmall,
    /// `beta <= 0` or `nan`.
    BetaTooSmall,
}

impl fmt::Display for BetaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            BetaError::AlphaTooSmall => "alpha is not positive in beta distribution",
            BetaError::BetaTooSmall => "beta is not positive in beta distribution",
        })
    }
}

impl error::Error for BetaError {}

impl<N: Float> Beta<N>
where
    StandardNormal: Distribution<N>,
    Exp1: Distribution<N>,
    Open01: Distribution<N>,
{
    /// Construct an object representing the `Beta(alpha, beta)`
    /// distribution.
    pub fn new(alpha: N, beta: N) -> Result<Beta<N>, BetaError> {
        Ok(Beta {
            gamma_a: Gamma::new(alpha, N::from(1.)).map_err(|_| BetaError::AlphaTooSmall)?,
            gamma_b: Gamma::new(beta, N::from(1.)).map_err(|_| BetaError::BetaTooSmall)?,
        })
    }
}

impl<N: Float> Distribution<N> for Beta<N>
where
    StandardNormal: Distribution<N>,
    Exp1: Distribution<N>,
    Open01: Distribution<N>,
{
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> N {
        let x = self.gamma_a.sample(rng);
        let y = self.gamma_b.sample(rng);
        x / (x + y)
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
    fn test_f() {
        let f = FisherF::new(2.0, 32.0).unwrap();
        let mut rng = crate::test::rng(204);
        for _ in 0..1000 {
            f.sample(&mut rng);
        }
    }

    #[test]
    fn test_t() {
        let t = StudentT::new(11.0).unwrap();
        let mut rng = crate::test::rng(205);
        for _ in 0..1000 {
            t.sample(&mut rng);
        }
    }

    #[test]
    fn test_beta() {
        let beta = Beta::new(1.0, 2.0).unwrap();
        let mut rng = crate::test::rng(201);
        for _ in 0..1000 {
            beta.sample(&mut rng);
        }
    }

    #[test]
    #[should_panic]
    fn test_beta_invalid_dof() {
        Beta::new(0., 0.).unwrap();
    }

    #[test]
    fn value_stability() {
        fn test_samples<N: Float + core::fmt::Debug, D: Distribution<N>>(
            distr: D, zero: N, expected: &[N],
        ) {
            let mut rng = crate::test::rng(223);
            let mut buf = [zero; 4];
            for x in &mut buf {
                *x = rng.sample(&distr);
            }
            assert_eq!(buf, expected);
        }

        // Gamma has 3 cases: shape == 1, shape < 1, shape > 1
        test_samples(Gamma::new(1.0, 5.0).unwrap(), 0f32, &[
            5.398085, 9.162783, 0.2300583, 1.7235851,
        ]);
        test_samples(Gamma::new(0.8, 5.0).unwrap(), 0f32, &[
            0.5051203, 0.9048302, 3.095812, 1.8566116,
        ]);
        test_samples(Gamma::new(1.1, 5.0).unwrap(), 0f64, &[
            7.783878094584059,
            1.4939528171618057,
            8.638017638857592,
            3.0949337228829004,
        ]);

        // ChiSquared has 2 cases: k == 1, k != 1
        test_samples(ChiSquared::new(1.0).unwrap(), 0f64, &[
            0.4893526200348249,
            1.635249736808788,
            0.5013580219361969,
            0.1457735613733489,
        ]);
        test_samples(ChiSquared::new(0.1).unwrap(), 0f64, &[
            0.014824404726978617,
            0.021602123937134326,
            0.0000003431429746851693,
            0.00000002291755769542258,
        ]);
        test_samples(ChiSquared::new(10.0).unwrap(), 0f32, &[
            12.693656, 6.812016, 11.082001, 12.436167,
        ]);

        // FisherF has same special cases as ChiSquared on each param
        test_samples(FisherF::new(1.0, 13.5).unwrap(), 0f32, &[
            0.32283646,
            0.048049655,
            0.0788893,
            1.817178,
        ]);
        test_samples(FisherF::new(1.0, 1.0).unwrap(), 0f32, &[
            0.29925257, 3.4392934, 9.567652, 0.020074,
        ]);
        test_samples(FisherF::new(0.7, 13.5).unwrap(), 0f64, &[
            3.3196593155045124,
            0.3409169916262829,
            0.03377989856426519,
            0.00004041672861036937,
        ]);

        // StudentT has same special cases as ChiSquared
        test_samples(StudentT::new(1.0).unwrap(), 0f32, &[
            0.54703987,
            -1.8545331,
            3.093162,
            -0.14168274,
        ]);
        test_samples(StudentT::new(1.1).unwrap(), 0f64, &[
            0.7729195887949754,
            1.2606210611616204,
            -1.7553606501113175,
            -2.377641221169782,
        ]);

        // Beta has same special cases as Gamma on each param
        test_samples(Beta::new(1.0, 0.8).unwrap(), 0f32, &[
            0.6444564, 0.357635, 0.4110078, 0.7347192,
        ]);
        test_samples(Beta::new(0.7, 1.2).unwrap(), 0f64, &[
            0.6433129944095513,
            0.5373371199711573,
            0.10313293199269491,
            0.002472280249144378,
        ]);
    }
}
