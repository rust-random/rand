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
//! bounds. Distributions use the `Distribution` trait to yield values: call
//! `dist.sample(&mut rng)` to get a random variable.
//!
//! TODO: is it worth exposing both submodules and re-exporting their members?

use Rng;

pub use self::default::Default;
pub use self::uniform::{uniform, codepoint, ascii_word_char};
pub use self::uniform::{Uniform, Uniform01, Open01, Closed01};
pub use self::range::{range, Range};

#[cfg(feature="std")]
pub use self::gamma::{Gamma, ChiSquared, FisherF, StudentT};
#[cfg(feature="std")]
pub use self::normal::{Normal, LogNormal};
#[cfg(feature="std")]
pub use self::exponential::Exp;

mod default;
mod uniform;
#[cfg(feature="std")]
mod ziggurat_tables;

pub mod range;
pub mod range2;

#[cfg(feature="std")]
pub mod gamma;
#[cfg(feature="std")]
pub mod normal;
#[cfg(feature="std")]
pub mod exponential;


/// Return a bool with a 1 in n chance of being true
/// 
/// This uses [`range`] internally, so for repeated uses it would be faster to
/// create a `Range` distribution and test its samples:
/// `range.sample(rng) == 0`.
///
/// # Example
///
/// ```rust
/// use rand::distributions::weighted_bool;
///
/// let mut rng = rand::thread_rng();
/// println!("{}", weighted_bool(3, &mut rng));
/// ```
pub fn weighted_bool<R: Rng+?Sized>(n: u32, rng: &mut R) -> bool {
    n <= 1 || range(0, n, rng) == 0
}

/// Types (distributions) that can be used to create a random instance of `T`.
pub trait Distribution<T> {
    /// Generate a random value of `T`, using `rng` as the
    /// source of randomness.
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> T;
}

/// Generic trait for sampling random values from some distribution
pub trait Rand<Dist> {
    fn rand<R: Rng+?Sized>(rng: &mut R, dist: Dist) -> Self;
}

impl<T, D: Distribution<T>> Rand<D> for T {
    fn rand<R: Rng+?Sized>(rng: &mut R, dist: D) -> Self {
        dist.sample(rng)
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
fn ziggurat<R: Rng+?Sized, P, Z>(
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
        let bits: u64 = uniform(rng);
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
        if f_tab[i + 1] + (f_tab[i] - f_tab[i + 1]) * f64::rand(rng, Uniform01) < pdf(x) {
            return x;
        }
    }
}

#[cfg(test)]
mod test {
    use {Rng, thread_rng};
    use distributions::weighted_bool;

    #[test]
    fn test_fn_weighted_bool() {
        let mut r = thread_rng();
        assert_eq!(weighted_bool(0, &mut r), true);
        let s: &mut Rng = &mut r;
        assert_eq!(weighted_bool(1, s), true);
    }
}
