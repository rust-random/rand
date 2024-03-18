// Copyright 2018 Developers of the Rand project.
// Copyright 2013-2017 The Rust Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Utilities for random number generation
//!
//! Rand provides utilities to generate random numbers, to convert them to
//! useful types and distributions, and some randomness-related algorithms.
//!
//! # Quick Start
//!
//! To get you started quickly, the easiest and highest-level way to get
//! a random value is to use [`random()`]; alternatively you can use
//! [`thread_rng()`]. The [`Rng`] trait provides a useful API on all RNGs, while
//! the [`distributions`] and [`seq`] modules provide further
//! functionality on top of RNGs.
//!
//! ```
//! use rand::prelude::*;
//!
//! if rand::random() { // generates a boolean
//!     // Try printing a random unicode code point (probably a bad idea)!
//!     println!("char: {}", rand::random::<char>());
//! }
//!
//! let mut rng = rand::thread_rng();
//! let y: f64 = rng.gen(); // generates a float between 0 and 1
//!
//! let mut nums: Vec<i32> = (1..100).collect();
//! nums.shuffle(&mut rng);
//! ```
//!
//! # The Book
//!
//! For the user guide and further documentation, please read
//! [The Rust Rand Book](https://rust-random.github.io/book).

#![doc(
    html_logo_url = "https://www.rust-lang.org/logos/rust-logo-128x128-blk.png",
    html_favicon_url = "https://www.rust-lang.org/favicon.ico",
    html_root_url = "https://rust-random.github.io/rand/"
)]
#![deny(missing_docs)]
#![deny(missing_debug_implementations)]
#![doc(test(attr(allow(unused_variables), deny(warnings))))]
#![no_std]
#![cfg_attr(feature = "simd_support", feature(portable_simd))]
#![cfg_attr(doc_cfg, feature(doc_cfg))]
#![allow(
    clippy::float_cmp,
    clippy::neg_cmp_op_on_partial_ord,
    clippy::nonminimal_bool
)]

#[cfg(feature = "std")] extern crate std;
#[cfg(feature = "alloc")] extern crate alloc;

#[allow(unused)]
macro_rules! trace { ($($x:tt)*) => (
    #[cfg(feature = "log")] {
        log::trace!($($x)*)
    }
) }
#[allow(unused)]
macro_rules! debug { ($($x:tt)*) => (
    #[cfg(feature = "log")] {
        log::debug!($($x)*)
    }
) }
#[allow(unused)]
macro_rules! info { ($($x:tt)*) => (
    #[cfg(feature = "log")] {
        log::info!($($x)*)
    }
) }
#[allow(unused)]
macro_rules! warn { ($($x:tt)*) => (
    #[cfg(feature = "log")] {
        log::warn!($($x)*)
    }
) }
#[allow(unused)]
macro_rules! error { ($($x:tt)*) => (
    #[cfg(feature = "log")] {
        log::error!($($x)*)
    }
) }

// Re-exports from rand_core
pub use rand_core::{CryptoRng, Error, RngCore, SeedableRng};

// Public modules
pub mod distributions;
pub mod prelude;
mod rng;
pub mod rngs;
pub mod seq;

// Public exports
#[cfg(all(feature = "std", feature = "std_rng", feature = "getrandom"))]
pub use crate::rngs::thread::thread_rng;
pub use rng::{Fill, Rng};

#[cfg(all(feature = "std", feature = "std_rng", feature = "getrandom"))]
use crate::distributions::{Distribution, Standard};

/// Generates a random value using the thread-local random number generator.
///
/// This function is simply a shortcut for `thread_rng().gen()`:
///
/// -   See [`ThreadRng`] for documentation of the generator and security
/// -   See [`Standard`] for documentation of supported types and distributions
///
/// # Examples
///
/// ```
/// let x = rand::random::<u8>();
/// println!("{}", x);
///
/// let y = rand::random::<f64>();
/// println!("{}", y);
///
/// if rand::random() { // generates a boolean
///     println!("Better lucky than good!");
/// }
/// ```
///
/// If you're calling `random()` in a loop, caching the generator as in the
/// following example can increase performance.
///
/// ```
/// use rand::Rng;
///
/// let mut v = vec![1, 2, 3];
///
/// for x in v.iter_mut() {
///     *x = rand::random()
/// }
///
/// // can be made faster by caching thread_rng
///
/// let mut rng = rand::thread_rng();
///
/// for x in v.iter_mut() {
///     *x = rng.gen();
/// }
/// ```
///
/// [`Standard`]: distributions::Standard
/// [`ThreadRng`]: rngs::ThreadRng
#[cfg(all(feature = "std", feature = "std_rng", feature = "getrandom"))]
#[cfg_attr(doc_cfg, doc(cfg(all(feature = "std", feature = "std_rng", feature = "getrandom"))))]
#[inline]
pub fn random<T>() -> T
where Standard: Distribution<T> {
    thread_rng().gen()
}

#[cfg(test)]
mod test {
    use super::*;

    /// Construct a deterministic RNG with the given seed
    pub fn rng(seed: u64) -> impl RngCore {
        // For tests, we want a statistically good, fast, reproducible RNG.
        // PCG32 will do fine, and will be easy to embed if we ever need to.
        const INC: u64 = 11634580027462260723;
        rand_pcg::Pcg32::new(seed, INC)
    }

    #[test]
    #[cfg(all(feature = "std", feature = "std_rng", feature = "getrandom"))]
    fn test_random() {
        let _n: usize = random();
        let _f: f32 = random();
        let _o: Option<Option<i8>> = random();
        #[allow(clippy::type_complexity)]
        let _many: (
            (),
            (usize, isize, Option<(u32, (bool,))>),
            (u8, i8, u16, i16, u32, i32, u64, i64),
            (f32, (f64, (f64,))),
        ) = random();
    }
}
