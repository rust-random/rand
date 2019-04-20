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
//!   - [`UnitSphereSurface`] distribution
//!   - [`UnitCircle`] distribution

pub use rand::distributions::{Distribution, DistIter, Standard,
    Alphanumeric, Uniform, OpenClosed01, Open01, Bernoulli, weighted};

pub use self::unit_sphere::UnitSphereSurface;
pub use self::unit_circle::UnitCircle;
pub use self::gamma::{Gamma, Error as GammaError, ChiSquared, ChiSquaredError,
    FisherF, FisherFError, StudentT, Beta, BetaError};
pub use self::normal::{Normal, Error as NormalError, LogNormal, StandardNormal};
pub use self::exponential::{Exp, Error as ExpError, Exp1};
pub use self::pareto::{Pareto, Error as ParetoError};
pub use self::poisson::{Poisson, Error as PoissonError};
pub use self::binomial::{Binomial, Error as BinomialError};
pub use self::cauchy::{Cauchy, Error as CauchyError};
pub use self::dirichlet::{Dirichlet, Error as DirichletError};
pub use self::triangular::{Triangular, Error as TriangularError};
pub use self::weibull::{Weibull, Error as WeibullError};

mod unit_sphere;
mod unit_circle;
mod gamma;
mod normal;
mod exponential;
mod pareto;
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
    use rand::{RngCore, SeedableRng, rngs::StdRng};

    pub fn rng(seed: u64) -> impl RngCore {
        StdRng::seed_from_u64(seed)
    }
}
