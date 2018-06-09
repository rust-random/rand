// Copyright 2013-2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
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
//! documentation in the [`uniform` module]. Doing so enables generation of
//! values of type `T` with  [`Rng::gen_range`].
//!
//!
//! # Other distributions
//!
//! There are surprisingly many ways to uniformly generate random floats. A
//! range between 0 and 1 is standard, but the exact bounds (open vs closed)
//! and accuracy differ. In addition to the [`Standard`] distribution Rand offers
//! [`Open01`] and [`OpenClosed01`]. See [Floating point implementation] for
//! more details.
//!
//! [`Alphanumeric`] is a simple distribution to sample random letters and
//! numbers of the `char` type; in contrast [`Standard`] may sample any valid
//! `char`.
//!
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
//!   - [`Poisson`] distribution
//!   - [`Exp`]onential distribution, and [`Exp1`] as a primitive
//! - Gamma and derived distributions:
//!   - [`Gamma`] distribution
//!   - [`ChiSquared`] distribution
//!   - [`StudentT`] distribution
//!   - [`FisherF`] distribution
//!
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
//! [`Distribution`]: trait.Distribution.html
//! [`gen_range`]: ../trait.Rng.html#method.gen_range
//! [`gen`]: ../trait.Rng.html#method.gen
//! [`sample`]: ../trait.Rng.html#method.sample
//! [`new_inclusive`]: struct.Uniform.html#method.new_inclusive
//! [`random()`]: ../fn.random.html
//! [`Rng::gen_bool`]: ../trait.Rng.html#method.gen_bool
//! [`Rng::gen_range`]: ../trait.Rng.html#method.gen_range
//! [`Rng::gen()`]: ../trait.Rng.html#method.gen
//! [`Rng`]: ../trait.Rng.html
//! [`uniform` module]: uniform/index.html
//! [Floating point implementation]: struct.Standard.html#floating-point-implementation
// distributions
//! [`Alphanumeric`]: struct.Alphanumeric.html
//! [`Bernoulli`]: struct.Bernoulli.html
//! [`Binomial`]: struct.Binomial.html
//! [`Cauchy`]: struct.Cauchy.html
//! [`ChiSquared`]: struct.ChiSquared.html
//! [`Exp`]: struct.Exp.html
//! [`Exp1`]: struct.Exp1.html
//! [`FisherF`]: struct.FisherF.html
//! [`Gamma`]: struct.Gamma.html
//! [`LogNormal`]: struct.LogNormal.html
//! [`Normal`]: struct.Normal.html
//! [`Open01`]: struct.Open01.html
//! [`OpenClosed01`]: struct.OpenClosed01.html
//! [`Pareto`]: struct.Pareto.html
//! [`Poisson`]: struct.Poisson.html
//! [`Standard`]: struct.Standard.html
//! [`StandardNormal`]: struct.StandardNormal.html
//! [`StudentT`]: struct.StudentT.html
//! [`Uniform`]: struct.Uniform.html
//! [`Uniform::new`]: struct.Uniform.html#method.new
//! [`Uniform::new_inclusive`]: struct.Uniform.html#method.new_inclusive

use Rng;

#[doc(inline)] pub use self::other::Alphanumeric;
#[doc(inline)] pub use self::uniform::Uniform;
#[doc(inline)] pub use self::float::{OpenClosed01, Open01};
#[deprecated(since="0.5.0", note="use Uniform instead")]
pub use self::uniform::Uniform as Range;
#[cfg(feature="std")]
#[doc(inline)] pub use self::gamma::{Gamma, ChiSquared, FisherF, StudentT};
#[cfg(feature="std")]
#[doc(inline)] pub use self::normal::{Normal, LogNormal, StandardNormal};
#[cfg(feature="std")]
#[doc(inline)] pub use self::exponential::{Exp, Exp1};
#[cfg(feature="std")]
#[doc(inline)] pub use self::pareto::Pareto;
#[cfg(feature = "std")]
#[doc(inline)] pub use self::poisson::Poisson;
#[cfg(feature = "std")]
#[doc(inline)] pub use self::binomial::Binomial;
#[doc(inline)] pub use self::bernoulli::Bernoulli;
#[cfg(feature = "std")]
#[doc(inline)] pub use self::cauchy::Cauchy;

pub mod uniform;
#[cfg(feature="std")]
#[doc(hidden)] pub mod gamma;
#[cfg(feature="std")]
#[doc(hidden)] pub mod normal;
#[cfg(feature="std")]
#[doc(hidden)] pub mod exponential;
#[cfg(feature="std")]
#[doc(hidden)] pub mod pareto;
#[cfg(feature = "std")]
#[doc(hidden)] pub mod poisson;
#[cfg(feature = "std")]
#[doc(hidden)] pub mod binomial;
#[doc(hidden)] pub mod bernoulli;
#[cfg(feature = "std")]
#[doc(hidden)] pub mod cauchy;

mod float;
mod integer;
#[cfg(feature="std")]
mod log_gamma;
mod other;
#[cfg(feature="std")]
mod ziggurat_tables;
#[cfg(feature="std")]
use distributions::float::IntoFloat;

/// Types that can be used to create a random instance of `Support`.
#[deprecated(since="0.5.0", note="use Distribution instead")]
pub trait Sample<Support> {
    /// Generate a random value of `Support`, using `rng` as the
    /// source of randomness.
    fn sample<R: Rng>(&mut self, rng: &mut R) -> Support;
}

/// `Sample`s that do not require keeping track of state.
///
/// Since no state is recorded, each sample is (statistically)
/// independent of all others, assuming the `Rng` used has this
/// property.
#[allow(deprecated)]
#[deprecated(since="0.5.0", note="use Distribution instead")]
pub trait IndependentSample<Support>: Sample<Support> {
    /// Generate a random value.
    fn ind_sample<R: Rng>(&self, &mut R) -> Support;
}

/// DEPRECATED: Use `distributions::uniform` instead.
#[deprecated(since="0.5.0", note="use uniform instead")]
pub mod range {
    pub use distributions::uniform::Uniform as Range;
    pub use distributions::uniform::SampleUniform as SampleRange;
}

#[allow(deprecated)]
mod impls {
    use Rng;
    use distributions::{Distribution, Sample, IndependentSample,
            WeightedChoice};
    #[cfg(feature="std")]
    use distributions::exponential::Exp;
    #[cfg(feature="std")]
    use distributions::gamma::{Gamma, ChiSquared, FisherF, StudentT};
    #[cfg(feature="std")]
    use distributions::normal::{Normal, LogNormal};
    use distributions::range::{Range, SampleRange};
    
    impl<'a, T: Clone> Sample<T> for WeightedChoice<'a, T> {
        fn sample<R: Rng>(&mut self, rng: &mut R) -> T {
            Distribution::sample(self, rng)
        }
    }
    impl<'a, T: Clone> IndependentSample<T> for WeightedChoice<'a, T> {
        fn ind_sample<R: Rng>(&self, rng: &mut R) -> T {
            Distribution::sample(self, rng)
        }
    }
    
    impl<T: SampleRange> Sample<T> for Range<T> {
        fn sample<R: Rng>(&mut self, rng: &mut R) -> T {
            Distribution::sample(self, rng)
        }
    }
    impl<T: SampleRange> IndependentSample<T> for Range<T> {
        fn ind_sample<R: Rng>(&self, rng: &mut R) -> T {
            Distribution::sample(self, rng)
        }
    }
    
    #[cfg(feature="std")]
    macro_rules! impl_f64 {
        ($($name: ident), *) => {
            $(
                impl Sample<f64> for $name {
                    fn sample<R: Rng>(&mut self, rng: &mut R) -> f64 {
                        Distribution::sample(self, rng)
                    }
                }
                impl IndependentSample<f64> for $name {
                    fn ind_sample<R: Rng>(&self, rng: &mut R) -> f64 {
                        Distribution::sample(self, rng)
                    }
                }
            )*
        }
    }
    #[cfg(feature="std")]
    impl_f64!(Exp, Gamma, ChiSquared, FisherF, StudentT, Normal, LogNormal);
}

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
/// [`Rng`]: ../trait.Rng.html
/// [`sample_iter`]: trait.Distribution.html#method.sample_iter
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
/// [`Distribution`]: trait.Distribution.html
/// [`sample_iter`]: trait.Distribution.html#method.sample_iter
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
/// [`Open01`]: struct.Open01.html
/// [`OpenClosed01`]: struct.OpenClosed01.html
/// [`Uniform`]: uniform/struct.Uniform.html
#[derive(Clone, Copy, Debug)]
pub struct Standard;

#[allow(deprecated)]
impl<T> ::Rand for T where Standard: Distribution<T> {
    fn rand<R: Rng>(rng: &mut R) -> Self {
        Standard.sample(rng)
    }
}


/// A value with a particular weight for use with `WeightedChoice`.
#[derive(Copy, Clone, Debug)]
pub struct Weighted<T> {
    /// The numerical weight of this item
    pub weight: u32,
    /// The actual item which is being weighted
    pub item: T,
}

/// A distribution that selects from a finite collection of weighted items.
///
/// Each item has an associated weight that influences how likely it
/// is to be chosen: higher weight is more likely.
///
/// The `Clone` restriction is a limitation of the `Distribution` trait.
/// Note that `&T` is (cheaply) `Clone` for all `T`, as is `u32`, so one can
/// store references or indices into another vector.
///
/// # Example
///
/// ```
/// use rand::distributions::{Weighted, WeightedChoice, Distribution};
///
/// let mut items = vec!(Weighted { weight: 2, item: 'a' },
///                      Weighted { weight: 4, item: 'b' },
///                      Weighted { weight: 1, item: 'c' });
/// let wc = WeightedChoice::new(&mut items);
/// let mut rng = rand::thread_rng();
/// for _ in 0..16 {
///      // on average prints 'a' 4 times, 'b' 8 and 'c' twice.
///      println!("{}", wc.sample(&mut rng));
/// }
/// ```
#[derive(Debug)]
pub struct WeightedChoice<'a, T:'a> {
    items: &'a mut [Weighted<T>],
    weight_range: Uniform<u32>,
}

impl<'a, T: Clone> WeightedChoice<'a, T> {
    /// Create a new `WeightedChoice`.
    ///
    /// Panics if:
    ///
    /// - `items` is empty
    /// - the total weight is 0
    /// - the total weight is larger than a `u32` can contain.
    pub fn new(items: &'a mut [Weighted<T>]) -> WeightedChoice<'a, T> {
        // strictly speaking, this is subsumed by the total weight == 0 case
        assert!(!items.is_empty(), "WeightedChoice::new called with no items");

        let mut running_total: u32 = 0;

        // we convert the list from individual weights to cumulative
        // weights so we can binary search. This *could* drop elements
        // with weight == 0 as an optimisation.
        for item in items.iter_mut() {
            running_total = match running_total.checked_add(item.weight) {
                Some(n) => n,
                None => panic!("WeightedChoice::new called with a total weight \
                               larger than a u32 can contain")
            };

            item.weight = running_total;
        }
        assert!(running_total != 0, "WeightedChoice::new called with a total weight of 0");

        WeightedChoice {
            items,
            // we're likely to be generating numbers in this range
            // relatively often, so might as well cache it
            weight_range: Uniform::new(0, running_total)
        }
    }
}

impl<'a, T: Clone> Distribution<T> for WeightedChoice<'a, T> {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> T {
        // we want to find the first element that has cumulative
        // weight > sample_weight, which we do by binary since the
        // cumulative weights of self.items are sorted.

        // choose a weight in [0, total_weight)
        let sample_weight = self.weight_range.sample(rng);

        // short circuit when it's the first item
        if sample_weight < self.items[0].weight {
            return self.items[0].item.clone();
        }

        let mut idx = 0;
        let mut modifier = self.items.len();

        // now we know that every possibility has an element to the
        // left, so we can just search for the last element that has
        // cumulative weight <= sample_weight, then the next one will
        // be "it". (Note that this greatest element will never be the
        // last element of the vector, since sample_weight is chosen
        // in [0, total_weight) and the cumulative weight of the last
        // one is exactly the total weight.)
        while modifier > 1 {
            let i = idx + modifier / 2;
            if self.items[i].weight <= sample_weight {
                // we're small, so look to the right, but allow this
                // exact element still.
                idx = i;
                // we need the `/ 2` to round up otherwise we'll drop
                // the trailing elements when `modifier` is odd.
                modifier += 1;
            } else {
                // otherwise we're too big, so go left. (i.e. do
                // nothing)
            }
            modifier /= 2;
        }
        self.items[idx + 1].item.clone()
    }
}

/// Sample a random number using the Ziggurat method (specifically the
/// ZIGNOR variant from Doornik 2005). Most of the arguments are
/// directly from the paper:
///
/// * `rng`: source of randomness
/// * `symmetric`: whether this is a symmetric distribution, or one-sided with P(x < 0) = 0.
/// * `X`: the $x_i$ abscissae.
/// * `F`: precomputed values of the PDF at the $x_i$, (i.e. $f(x_i)$)
/// * `F_DIFF`: precomputed values of $f(x_i) - f(x_{i+1})$
/// * `pdf`: the probability density function
/// * `zero_case`: manual sampling from the tail when we chose the
///    bottom box (i.e. i == 0)

// the perf improvement (25-50%) is definitely worth the extra code
// size from force-inlining.
#[cfg(feature="std")]
#[inline(always)]
fn ziggurat<R: Rng + ?Sized, P, Z>(
            rng: &mut R,
            symmetric: bool,
            x_tab: ziggurat_tables::ZigTable,
            f_tab: ziggurat_tables::ZigTable,
            mut pdf: P,
            mut zero_case: Z)
            -> f64 where P: FnMut(f64) -> f64, Z: FnMut(&mut R, f64) -> f64 {
    loop {
        // As an optimisation we re-implement the conversion to a f64.
        // From the remaining 12 most significant bits we use 8 to construct `i`.
        // This saves us generating a whole extra random number, while the added
        // precision of using 64 bits for f64 does not buy us much.
        let bits = rng.next_u64();
        let i = bits as usize & 0xff;

        let u = if symmetric {
            // Convert to a value in the range [2,4) and substract to get [-1,1)
            // We can't convert to an open range directly, that would require
            // substracting `3.0 - EPSILON`, which is not representable.
            // It is possible with an extra step, but an open range does not
            // seem neccesary for the ziggurat algorithm anyway.
            (bits >> 12).into_float_with_exponent(1) - 3.0
        } else {
            // Convert to a value in the range [1,2) and substract to get (0,1)
            (bits >> 12).into_float_with_exponent(0)
            - (1.0 - ::core::f64::EPSILON / 2.0)
        };
        let x = u * x_tab[i];

        let test_x = if symmetric { x.abs() } else {x};

        // algebraically equivalent to |u| < x_tab[i+1]/x_tab[i] (or u < x_tab[i+1]/x_tab[i])
        if test_x < x_tab[i + 1] {
            return x;
        }
        if i == 0 {
            return zero_case(rng, u);
        }
        // algebraically equivalent to f1 + DRanU()*(f0 - f1) < 1
        if f_tab[i + 1] + (f_tab[i] - f_tab[i + 1]) * rng.gen::<f64>() < pdf(x) {
            return x;
        }
    }
}

#[cfg(test)]
mod tests {
    use Rng;
    use rngs::mock::StepRng;
    use super::{WeightedChoice, Weighted, Distribution};

    #[test]
    fn test_weighted_choice() {
        // this makes assumptions about the internal implementation of
        // WeightedChoice. It may fail when the implementation in
        // `distributions::uniform::UniformInt` changes.

        macro_rules! t {
            ($items:expr, $expected:expr) => {{
                let mut items = $items;
                let mut total_weight = 0;
                for item in &items { total_weight += item.weight; }

                let wc = WeightedChoice::new(&mut items);
                let expected = $expected;

                // Use extremely large steps between the random numbers, because
                // we test with small ranges and `UniformInt` is designed to prefer
                // the most significant bits.
                let mut rng = StepRng::new(0, !0 / (total_weight as u64));

                for &val in expected.iter() {
                    assert_eq!(wc.sample(&mut rng), val)
                }
            }}
        }

        t!([Weighted { weight: 1, item: 10}], [10]);

        // skip some
        t!([Weighted { weight: 0, item: 20},
            Weighted { weight: 2, item: 21},
            Weighted { weight: 0, item: 22},
            Weighted { weight: 1, item: 23}],
           [21, 21, 23]);

        // different weights
        t!([Weighted { weight: 4, item: 30},
            Weighted { weight: 3, item: 31}],
           [30, 31, 30, 31, 30, 31, 30]);

        // check that we're binary searching
        // correctly with some vectors of odd
        // length.
        t!([Weighted { weight: 1, item: 40},
            Weighted { weight: 1, item: 41},
            Weighted { weight: 1, item: 42},
            Weighted { weight: 1, item: 43},
            Weighted { weight: 1, item: 44}],
           [40, 41, 42, 43, 44]);
        t!([Weighted { weight: 1, item: 50},
            Weighted { weight: 1, item: 51},
            Weighted { weight: 1, item: 52},
            Weighted { weight: 1, item: 53},
            Weighted { weight: 1, item: 54},
            Weighted { weight: 1, item: 55},
            Weighted { weight: 1, item: 56}],
           [50, 54, 51, 55, 52, 56, 53]);
    }

    #[test]
    fn test_weighted_clone_initialization() {
        let initial : Weighted<u32> = Weighted {weight: 1, item: 1};
        let clone = initial.clone();
        assert_eq!(initial.weight, clone.weight);
        assert_eq!(initial.item, clone.item);
    }

    #[test] #[should_panic]
    fn test_weighted_clone_change_weight() {
        let initial : Weighted<u32> = Weighted {weight: 1, item: 1};
        let mut clone = initial.clone();
        clone.weight = 5;
        assert_eq!(initial.weight, clone.weight);
    }

    #[test] #[should_panic]
    fn test_weighted_clone_change_item() {
        let initial : Weighted<u32> = Weighted {weight: 1, item: 1};
        let mut clone = initial.clone();
        clone.item = 5;
        assert_eq!(initial.item, clone.item);

    }

    #[test] #[should_panic]
    fn test_weighted_choice_no_items() {
        WeightedChoice::<isize>::new(&mut []);
    }
    #[test] #[should_panic]
    fn test_weighted_choice_zero_weight() {
        WeightedChoice::new(&mut [Weighted { weight: 0, item: 0},
                                  Weighted { weight: 0, item: 1}]);
    }
    #[test] #[should_panic]
    fn test_weighted_choice_weight_overflows() {
        let x = ::core::u32::MAX / 2; // x + x + 2 is the overflow
        WeightedChoice::new(&mut [Weighted { weight: x, item: 0 },
                                  Weighted { weight: 1, item: 1 },
                                  Weighted { weight: x, item: 2 },
                                  Weighted { weight: 1, item: 3 }]);
    }
    
    #[test] #[allow(deprecated)]
    fn test_backwards_compat_sample() {
        use distributions::{Sample, IndependentSample};
        
        struct Constant<T> { val: T }
        impl<T: Copy> Sample<T> for Constant<T> {
            fn sample<R: Rng>(&mut self, _: &mut R) -> T { self.val }
        }
        impl<T: Copy> IndependentSample<T> for Constant<T> {
            fn ind_sample<R: Rng>(&self, _: &mut R) -> T { self.val }
        }
        
        let mut sampler = Constant{ val: 293 };
        assert_eq!(sampler.sample(&mut ::test::rng(233)), 293);
        assert_eq!(sampler.ind_sample(&mut ::test::rng(234)), 293);
    }
    
    #[cfg(feature="std")]
    #[test] #[allow(deprecated)]
    fn test_backwards_compat_exp() {
        use distributions::{IndependentSample, Exp};
        let sampler = Exp::new(1.0);
        sampler.ind_sample(&mut ::test::rng(235));
    }

    #[cfg(feature="std")]
    #[test]
    fn test_distributions_iter() {
        use distributions::Normal;
        let mut rng = ::test::rng(210);
        let distr = Normal::new(10.0, 10.0);
        let results: Vec<_> = distr.sample_iter(&mut rng).take(100).collect();
        println!("{:?}", results);
    }
}
