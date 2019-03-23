// Copyright 2018 Developers of the Rand project.
// Copyright 2013-2017 The Rust Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Generating random samples from probability distributions.
//!
//! This module is the home of the [`Distribution`] trait and several of its
//! implementations. It is the workhorse behind some of the convenient
//! functionality of the [`Rng`] trait, including [`gen`], [`gen_range`] and
//! of course [`sample`].
//!
//! Abstractly, a [probability distribution] describes the probability of
//! occurance of each value in its sample space.
//!
//! More concretely, an implementation of `Distribution<T>` for type `X` is an
//! algorithm for choosing values from the sample space (a subset of `T`)
//! according to the distribution `X` represents, using an external source of
//! randomness (an RNG supplied to the `sample` function).
//!
//! A type `X` may implement `Distribution<T>` for multiple types `T`.
//! Any type implementing [`Distribution`] is stateless (i.e. immutable),
//! but it may have internal parameters set at construction time (for example,
//! [`Uniform`] allows specification of its sample space as a range within `T`).
//!
//!
//! # The `Standard` distribution
//!
//! The [`Standard`] distribution is important to mention. This is the
//! distribution used by [`Rng::gen()`] and represents the "default" way to
//! produce a random value for many different types, including most primitive
//! types, tuples, arrays, and a few derived types. See the documentation of
//! [`Standard`] for more details.
//!
//! Implementing `Distribution<T>` for [`Standard`] for user types `T` makes it
//! possible to generate type `T` with [`Rng::gen()`], and by extension also
//! with the [`random()`] function.
//!
//!
//! # Distribution to sample from a `Uniform` range
//!
//! The [`Uniform`] distribution is more flexible than [`Standard`], but also
//! more specialised: it supports fewer target types, but allows the sample
//! space to be specified as an arbitrary range within its target type `T`.
//! Both [`Standard`] and [`Uniform`] are in some sense uniform distributions.
//!
//! Values may be sampled from this distribution using [`Rng::gen_range`] or
//! by creating a distribution object with [`Uniform::new`],
//! [`Uniform::new_inclusive`] or `From<Range>`. When the range limits are not
//! known at compile time it is typically faster to reuse an existing
//! distribution object than to call [`Rng::gen_range`].
//!
//! User types `T` may also implement `Distribution<T>` for [`Uniform`],
//! although this is less straightforward than for [`Standard`] (see the
//! documentation in the [`uniform`] module. Doing so enables generation of
//! values of type `T` with  [`Rng::gen_range`].
//!
//!
//! # Other distributions
//!
//! There are surprisingly many ways to uniformly generate random floats. A
//! range between 0 and 1 is standard, but the exact bounds (open vs closed)
//! and accuracy differ. In addition to the [`Standard`] distribution Rand offers
//! [`Open01`] and [`OpenClosed01`]. See "Floating point implementation" section of
//! [`Standard`] documentation for more details.
//!
//! [`Alphanumeric`] is a simple distribution to sample random letters and
//! numbers of the `char` type; in contrast [`Standard`] may sample any valid
//! `char`.
//!
//! [`WeightedIndex`] can be used to do weighted sampling from a set of items,
//! such as from an array.
//!
//! # Non-uniform probability distributions
//!
//! Rand currently provides the following probability distributions:
//!
//! - Related to real-valued quantities that grow linearly
//!   (e.g. errors, offsets):
//!   - [`Normal`] distribution, and [`StandardNormal`] as a primitive
//!   - [`Cauchy`] distribution
//! - Related to Bernoulli trials (yes/no events, with a given probability):
//!   - [`Binomial`] distribution
//!   - [`Bernoulli`] distribution, similar to [`Rng::gen_bool`].
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
//!
//! # Examples
//!
//! Sampling from a distribution:
//!
//! ```
//! use rand::{thread_rng, Rng};
//! use rand::distributions::Exp;
//!
//! let exp = Exp::new(2.0);
//! let v = thread_rng().sample(exp);
//! println!("{} is from an Exp(2) distribution", v);
//! ```
//!
//! Implementing the [`Standard`] distribution for a user type:
//!
//! ```
//! # #![allow(dead_code)]
//! use rand::Rng;
//! use rand::distributions::{Distribution, Standard};
//!
//! struct MyF32 {
//!     x: f32,
//! }
//!
//! impl Distribution<MyF32> for Standard {
//!     fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> MyF32 {
//!         MyF32 { x: rng.gen() }
//!     }
//! }
//! ```
//!
//!
//! [probability distribution]: https://en.wikipedia.org/wiki/Probability_distribution
//! [`gen_range`]: Rng::gen_range
//! [`gen`]: Rng::gen
//! [`sample`]: Rng::sample
//! [`new_inclusive`]: Uniform::new_inclusive
//! [`Alphanumeric`]: distributions::Alphanumeric
//! [`Bernoulli`]: distributions::Bernoulli
//! [`Beta`]: distributions::Beta
//! [`Binomial`]: distributions::Binomial
//! [`Cauchy`]: distributions::Cauchy
//! [`ChiSquared`]: distributions::ChiSquared
//! [`Dirichlet`]: distributions::Dirichlet
//! [`Exp`]: distributions::Exp
//! [`Exp1`]: distributions::Exp1
//! [`FisherF`]: distributions::FisherF
//! [`Gamma`]: distributions::Gamma
//! [`LogNormal`]: distributions::LogNormal
//! [`Normal`]: distributions::Normal
//! [`Open01`]: distributions::Open01
//! [`OpenClosed01`]: distributions::OpenClosed01
//! [`Pareto`]: distributions::Pareto
//! [`Poisson`]: distributions::Poisson
//! [`Standard`]: distributions::Standard
//! [`StandardNormal`]: distributions::StandardNormal
//! [`StudentT`]: distributions::StudentT
//! [`Triangular`]: distributions::Triangular
//! [`Uniform`]: distributions::Uniform
//! [`Uniform::new`]: distributions::Uniform::new
//! [`Uniform::new_inclusive`]: distributions::Uniform::new_inclusive
//! [`UnitSphereSurface`]: distributions::UnitSphereSurface
//! [`UnitCircle`]: distributions::UnitCircle
//! [`Weibull`]: distributions::Weibull
//! [`WeightedIndex`]: distributions::WeightedIndex

#[cfg(any(rustc_1_26, features="nightly"))]
use core::iter;
use Rng;

pub use self::other::Alphanumeric;
#[doc(inline)] pub use self::uniform::Uniform;
pub use self::float::{OpenClosed01, Open01};
pub use self::bernoulli::Bernoulli;
#[cfg(feature="alloc")] pub use self::weighted::{WeightedIndex, WeightedError};
#[cfg(feature="std")] pub use self::unit_sphere::UnitSphereSurface;
#[cfg(feature="std")] pub use self::unit_circle::UnitCircle;
#[cfg(feature="std")] pub use self::gamma::{Gamma, ChiSquared, FisherF,
    StudentT, Beta};
#[cfg(feature="std")] pub use self::normal::{Normal, LogNormal, StandardNormal};
#[cfg(feature="std")] pub use self::exponential::{Exp, Exp1};
#[cfg(feature="std")] pub use self::pareto::Pareto;
#[cfg(feature="std")] pub use self::poisson::Poisson;
#[cfg(feature="std")] pub use self::binomial::Binomial;
#[cfg(feature="std")] pub use self::cauchy::Cauchy;
#[cfg(feature="std")] pub use self::dirichlet::Dirichlet;
#[cfg(feature="std")] pub use self::triangular::Triangular;
#[cfg(feature="std")] pub use self::weibull::Weibull;

pub mod uniform;
mod bernoulli;
#[cfg(feature="alloc")] mod weighted;
#[cfg(feature="std")] mod unit_sphere;
#[cfg(feature="std")] mod unit_circle;
#[cfg(feature="std")] mod gamma;
#[cfg(feature="std")] mod normal;
#[cfg(feature="std")] mod exponential;
#[cfg(feature="std")] mod pareto;
#[cfg(feature="std")] mod poisson;
#[cfg(feature="std")] mod binomial;
#[cfg(feature="std")] mod cauchy;
#[cfg(feature="std")] mod dirichlet;
#[cfg(feature="std")] mod triangular;
#[cfg(feature="std")] mod weibull;

mod float;
mod integer;
mod other;
mod utils;
#[cfg(feature="std")] mod ziggurat_tables;

/// Types (distributions) that can be used to create a random instance of `T`.
///
/// It is possible to sample from a distribution through both the
/// `Distribution` and [`Rng`] traits, via `distr.sample(&mut rng)` and
/// `rng.sample(distr)`. They also both offer the [`sample_iter`] method, which
/// produces an iterator that samples from the distribution.
///
/// All implementations are expected to be immutable; this has the significant
/// advantage of not needing to consider thread safety, and for most
/// distributions efficient state-less sampling algorithms are available.
///
/// [`sample_iter`]: Distribution::method.sample_iter
pub trait Distribution<T> {
    /// Generate a random value of `T`, using `rng` as the source of randomness.
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> T;

    /// Create an iterator that generates random values of `T`, using `rng` as
    /// the source of randomness.
    ///
    /// # Example
    ///
    /// ```
    /// use rand::thread_rng;
    /// use rand::distributions::{Distribution, Alphanumeric, Uniform, Standard};
    ///
    /// let mut rng = thread_rng();
    ///
    /// // Vec of 16 x f32:
    /// let v: Vec<f32> = Standard.sample_iter(&mut rng).take(16).collect();
    ///
    /// // String:
    /// let s: String = Alphanumeric.sample_iter(&mut rng).take(7).collect();
    ///
    /// // Dice-rolling:
    /// let die_range = Uniform::new_inclusive(1, 6);
    /// let mut roll_die = die_range.sample_iter(&mut rng);
    /// while roll_die.next().unwrap() != 6 {
    ///     println!("Not a 6; rolling again!");
    /// }
    /// ```
    fn sample_iter<'a, R>(&'a self, rng: &'a mut R) -> DistIter<'a, Self, R, T>
        where Self: Sized, R: Rng
    {
        DistIter {
            distr: self,
            rng: rng,
            phantom: ::core::marker::PhantomData,
        }
    }
}

impl<'a, T, D: Distribution<T>> Distribution<T> for &'a D {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> T {
        (*self).sample(rng)
    }
}


/// An iterator that generates random values of `T` with distribution `D`,
/// using `R` as the source of randomness.
///
/// This `struct` is created by the [`sample_iter`] method on [`Distribution`].
/// See its documentation for more.
///
/// [`sample_iter`]: Distribution::sample_iter
#[derive(Debug)]
pub struct DistIter<'a, D: 'a, R: 'a, T> {
    distr: &'a D,
    rng: &'a mut R,
    phantom: ::core::marker::PhantomData<T>,
}

impl<'a, D, R, T> Iterator for DistIter<'a, D, R, T>
    where D: Distribution<T>, R: Rng + 'a
{
    type Item = T;

    #[inline(always)]
    fn next(&mut self) -> Option<T> {
        Some(self.distr.sample(self.rng))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::max_value(), None)
    }
}

#[cfg(rustc_1_26)]
impl<'a, D, R, T> iter::FusedIterator for DistIter<'a, D, R, T>
    where D: Distribution<T>, R: Rng + 'a {}

#[cfg(features = "nightly")]
impl<'a, D, R, T> iter::TrustedLen for DistIter<'a, D, R, T>
    where D: Distribution<T>, R: Rng + 'a {}


/// A generic random value distribution, implemented for many primitive types.
/// Usually generates values with a numerically uniform distribution, and with a
/// range appropriate to the type.
///
/// ## Built-in Implementations
///
/// Assuming the provided `Rng` is well-behaved, these implementations
/// generate values with the following ranges and distributions:
///
/// * Integers (`i32`, `u32`, `isize`, `usize`, etc.): Uniformly distributed
///   over all values of the type.
/// * `char`: Uniformly distributed over all Unicode scalar values, i.e. all
///   code points in the range `0...0x10_FFFF`, except for the range
///   `0xD800...0xDFFF` (the surrogate code points). This includes
///   unassigned/reserved code points.
/// * `bool`: Generates `false` or `true`, each with probability 0.5.
/// * Floating point types (`f32` and `f64`): Uniformly distributed in the
///   half-open range `[0, 1)`. See notes below.
/// * Wrapping integers (`Wrapping<T>`), besides the type identical to their
///   normal integer variants.
///
/// The following aggregate types also implement the distribution `Standard` as
/// long as their component types implement it:
///
/// * Tuples and arrays: Each element of the tuple or array is generated
///   independently, using the `Standard` distribution recursively.
/// * `Option<T>` where `Standard` is implemented for `T`: Returns `None` with
///   probability 0.5; otherwise generates a random `x: T` and returns `Some(x)`.
///
/// # Example
/// ```
/// use rand::prelude::*;
/// use rand::distributions::Standard;
///
/// let val: f32 = SmallRng::from_entropy().sample(Standard);
/// println!("f32 from [0, 1): {}", val);
/// ```
///
/// # Floating point implementation
/// The floating point implementations for `Standard` generate a random value in
/// the half-open interval `[0, 1)`, i.e. including 0 but not 1.
///
/// All values that can be generated are of the form `n * ε/2`. For `f32`
/// the 23 most significant random bits of a `u32` are used and for `f64` the
/// 53 most significant bits of a `u64` are used. The conversion uses the
/// multiplicative method: `(rng.gen::<$uty>() >> N) as $ty * (ε/2)`.
///
/// See also: [`Open01`] which samples from `(0, 1)`, [`OpenClosed01`] which
/// samples from `(0, 1]` and `Rng::gen_range(0, 1)` which also samples from
/// `[0, 1)`. Note that `Open01` and `gen_range` (which uses [`Uniform`]) use
/// transmute-based methods which yield 1 bit less precision but may perform
/// faster on some architectures (on modern Intel CPUs all methods have
/// approximately equal performance).
///
/// [`Uniform`]: uniform::Uniform
#[derive(Clone, Copy, Debug)]
pub struct Standard;


#[cfg(all(test, feature = "std"))]
mod tests {
    use super::Distribution;

    #[test]
    fn test_distributions_iter() {
        use distributions::Normal;
        let mut rng = ::test::rng(210);
        let distr = Normal::new(10.0, 10.0);
        let results: Vec<_> = distr.sample_iter(&mut rng).take(100).collect();
        println!("{:?}", results);
    }
}
