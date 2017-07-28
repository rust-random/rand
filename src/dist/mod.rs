// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Sampling from random distributions.
//!
//! A distribution may have internal state describing the distribution of
//! generated values; for example `Range` needs to know its upper and lower
//! bounds. Distributions use the `Sample` trait to yield values: call
//! `dist.sample(&mut rng)` to get a random variable.

use std::marker;

use {Rng, Rand};

pub use self::range::Range;
pub use self::gamma::{Gamma, ChiSquared, FisherF, StudentT};
pub use self::normal::{Normal, LogNormal};
pub use self::exponential::Exp;

pub mod range;
pub mod gamma;
pub mod normal;
pub mod exponential;
pub mod weighted;

/// Types (distributions) that can be used to create a random instance of `T`.
pub trait Sample<T> {
    /// Generate a random value of `T`, using `rng` as the
    /// source of randomness.
    fn sample<R: Rng>(&self, rng: &mut R) -> T;
}


/// A wrapper for generating types that implement `Rand` via the
/// `Sample` trait.
#[derive(Debug)]
pub struct RandSample<T> {
    _marker: marker::PhantomData<fn() -> T>,
}

impl<T> Copy for RandSample<T> {}
impl<T> Clone for RandSample<T> {
    fn clone(&self) -> Self { *self }
}

impl<T: Rand> Sample<T> for RandSample<T> {
    fn sample<R: Rng>(&self, rng: &mut R) -> T {
        rng.gen()
    }
}

impl<T> RandSample<T> {
    pub fn new() -> RandSample<T> {
        RandSample { _marker: marker::PhantomData }
    }
}

mod ziggurat_tables;

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
#[inline(always)]
fn ziggurat<R: Rng, P, Z>(
            rng: &mut R,
            symmetric: bool,
            x_tab: ziggurat_tables::ZigTable,
            f_tab: ziggurat_tables::ZigTable,
            mut pdf: P,
            mut zero_case: Z)
            -> f64 where P: FnMut(f64) -> f64, Z: FnMut(&mut R, f64) -> f64 {
    const SCALE: f64 = (1u64 << 53) as f64;
    loop {
        // reimplement the f64 generation as an optimisation suggested
        // by the Doornik paper: we have a lot of precision-space
        // (i.e. there are 11 bits of the 64 of a u64 to use after
        // creating a f64), so we might as well reuse some to save
        // generating a whole extra random number. (Seems to be 15%
        // faster.)
        //
        // This unfortunately misses out on the benefits of direct
        // floating point generation if an RNG like dSMFT is
        // used. (That is, such RNGs create floats directly, highly
        // efficiently and overload next_f32/f64, so by not calling it
        // this may be slower than it would be otherwise.)
        // FIXME: investigate/optimise for the above.
        let bits: u64 = rng.gen();
        let i = (bits & 0xff) as usize;
        let f = (bits >> 11) as f64 / SCALE;

        // u is either U(-1, 1) or U(0, 1) depending on if this is a
        // symmetric distribution or not.
        let u = if symmetric {2.0 * f - 1.0} else {f};
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
