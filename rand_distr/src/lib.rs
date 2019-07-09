// Copyright 2019 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![doc(html_logo_url = "https://www.rust-lang.org/logos/rust-logo-128x128-blk.png",
       html_favicon_url = "https://www.rust-lang.org/favicon.ico",
       html_root_url = "https://rust-random.github.io/rand/")]

#![deny(missing_docs)]
#![deny(missing_debug_implementations)]

#![allow(clippy::excessive_precision, clippy::float_cmp, clippy::unreadable_literal)]
#![allow(clippy::neg_cmp_op_on_partial_ord)]  // suggested fix too verbose

//! Generating random samples from probability distributions.
//!
//! ## Re-exports
//!
//! This crate is a super-set of the [`rand::distributions`] module. See the
//! [`rand::distributions`] module documentation for an overview of the core
//! [`Distribution`] trait and implementations.
//!
//! The following are re-exported:
//! 
//! - The [`Distribution`] trait and [`DistIter`] helper type
//! - The [`Standard`], [`Alphanumeric`], [`Uniform`], [`OpenClosed01`], [`Open01`] and [`Bernoulli`] distributions
//! - The [`weighted`] sub-module
//!
//! ## Distributions
//!
//! This crate provides the following probability distributions:
//!
//! - Related to real-valued quantities that grow linearly
//!   (e.g. errors, offsets):
//!   - [`Normal`] distribution, and [`StandardNormal`] as a primitive
//!   - [`Cauchy`] distribution
//! - Related to Bernoulli trials (yes/no events, with a given probability):
//!   - [`Binomial`] distribution
//! - Related to positive real-valued quantities that grow exponentially
//!   (e.g. prices, incomes, populations):
//!   - [`LogNormal`] distribution
//! - Related to the occurrence of independent events at a given rate:
//!   - [`Pareto`] distribution
//!   - [`Poisson`] distribution
//!   - [`Exp`]onential distribution, and [`Exp1`] as a primitive
//!   - [`Weibull`] distribution
//! - Gamma and derived distributions:
//!   - [`Gamma`] distribution
//!   - [`ChiSquared`] distribution
//!   - [`StudentT`] distribution
//!   - [`FisherF`] distribution
//! - Triangular distribution:
//!   - [`Beta`] distribution
//!   - [`Triangular`] distribution
//! - Multivariate probability distributions
//!   - [`Dirichlet`] distribution
//!   - [`UnitSphere`] distribution
//!   - [`UnitBall`] distribution
//!   - [`UnitCircle`] distribution
//!   - [`UnitDisc`] distribution

pub use rand::distributions::{Distribution, DistIter, Standard,
    Alphanumeric, Uniform, OpenClosed01, Open01, Bernoulli, uniform, weighted};

pub use self::unit_sphere::UnitSphere;
pub use self::unit_ball::UnitBall;
pub use self::unit_circle::UnitCircle;
pub use self::unit_disc::UnitDisc;
pub use self::gamma::{Gamma, Error as GammaError, ChiSquared, ChiSquaredError,
    FisherF, FisherFError, StudentT, Beta, BetaError};
pub use self::normal::{Normal, Error as NormalError, LogNormal, StandardNormal};
pub use self::exponential::{Exp, Error as ExpError, Exp1};
pub use self::pareto::{Pareto, Error as ParetoError};
pub use self::pert::{Pert, PertError};
pub use self::poisson::{Poisson, Error as PoissonError};
pub use self::binomial::{Binomial, Error as BinomialError};
pub use self::cauchy::{Cauchy, Error as CauchyError};
pub use self::dirichlet::{Dirichlet, Error as DirichletError};
pub use self::triangular::{Triangular, TriangularError};
pub use self::weibull::{Weibull, Error as WeibullError};
pub use self::utils::Float;

mod unit_sphere;
mod unit_ball;
mod unit_circle;
mod unit_disc;
mod gamma;
mod normal;
mod exponential;
mod pareto;
mod pert;
mod poisson;
mod binomial;
mod cauchy;
mod dirichlet;
mod triangular;
mod weibull;
mod utils;
mod ziggurat_tables;

#[cfg(test)]
mod test {
    // Notes on testing
    // 
    // Testing random number distributions correctly is hard. The following
    // testing is desired:
    // 
    // - Construction: test initialisation with a few valid parameter sets.
    // - Erroneous usage: test that incorrect usage generates an error.
    // - Vector: test that usage with fixed inputs (including RNG) generates a
    //   fixed output sequence on all platforms.
    // - Correctness at fixed points (optional): using a specific mock RNG,
    //   check that specific values are sampled (e.g. end-points and median of
    //   distribution).
    // - Correctness of PDF (extra): generate a histogram of samples within a
    //   certain range, and check this approximates the PDF. These tests are
    //   expected to be expensive, and should be behind a feature-gate.
    //
    // TODO: Vector and correctness tests are largely absent so far.
    // NOTE: Some distributions have tests checking only that samples can be
    // generated. This is redundant with vector and correctness tests.

    /// Construct a deterministic RNG with the given seed
    pub fn rng(seed: u64) -> impl rand::RngCore {
        // For tests, we want a statistically good, fast, reproducible RNG.
        // PCG32 will do fine, and will be easy to embed if we ever need to.
        const INC: u64 = 11634580027462260723;
        rand_pcg::Pcg32::new(seed, INC)
    }
}
