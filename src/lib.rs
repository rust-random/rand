// Copyright 2013-2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Utilities for random number generation
//!
//! The key functions are `random()` and `Rng::gen()`. These are polymorphic and
//! so can be used to generate any type that implements `Rand`. Type inference
//! means that often a simple call to `rand::random()` or `rng.gen()` will
//! suffice, but sometimes an annotation is required, e.g.
//! `rand::random::<f64>()`.
//!
//! See the `distributions` submodule for sampling random numbers from
//! distributions like normal and exponential.
//!
//! # Usage
//!
//! This crate is [on crates.io](https://crates.io/crates/rand) and can be
//! used by adding `rand` to the dependencies in your project's `Cargo.toml`.
//!
//! ```toml
//! [dependencies]
//! rand = "0.4"
//! ```
//!
//! and this to your crate root:
//!
//! ```rust
//! extern crate rand;
//! ```
//!
//! # Thread-local RNG
//!
//! There is built-in support for a RNG associated with each thread stored
//! in thread-local storage. This RNG can be accessed via `thread_rng`, or
//! used implicitly via `random`. This RNG is normally randomly seeded
//! from an operating-system source of randomness, e.g. `/dev/urandom` on
//! Unix systems, and will automatically reseed itself from this source
//! after generating 32 KiB of random data.
//!
//! # Cryptographic security
//!
//! An application that requires an entropy source for cryptographic purposes
//! must use `OsRng`, which reads randomness from the source that the operating
//! system provides (e.g. `/dev/urandom` on Unixes or `CryptGenRandom()` on
//! Windows).
//! The other random number generators provided by this module are not suitable
//! for such purposes.
//!
//! *Note*: many Unix systems provide `/dev/random` as well as `/dev/urandom`.
//! This module uses `/dev/urandom` for the following reasons:
//!
//! -   On Linux, `/dev/random` may block if entropy pool is empty;
//!     `/dev/urandom` will not block.  This does not mean that `/dev/random`
//!     provides better output than `/dev/urandom`; the kernel internally runs a
//!     cryptographically secure pseudorandom number generator (CSPRNG) based on
//!     entropy pool for random number generation, so the "quality" of
//!     `/dev/random` is not better than `/dev/urandom` in most cases.  However,
//!     this means that `/dev/urandom` can yield somewhat predictable randomness
//!     if the entropy pool is very small, such as immediately after first
//!     booting.  Linux 3.17 added the `getrandom(2)` system call which solves
//!     the issue: it blocks if entropy pool is not initialized yet, but it does
//!     not block once initialized.  `OsRng` tries to use `getrandom(2)` if
//!     available, and use `/dev/urandom` fallback if not.  If an application
//!     does not have `getrandom` and likely to be run soon after first booting,
//!     or on a system with very few entropy sources, one should consider using
//!     `/dev/random` via `ReadRng`.
//! -   On some systems (e.g. FreeBSD, OpenBSD and Mac OS X) there is no
//!     difference between the two sources. (Also note that, on some systems
//!     e.g.  FreeBSD, both `/dev/random` and `/dev/urandom` may block once if
//!     the CSPRNG has not seeded yet.)
//!
//! # Examples
//!
//! ```rust
//! use rand::Rng;
//!
//! let mut rng = rand::thread_rng();
//! if rng.gen() { // random bool
//!     println!("i32: {}, u32: {}", rng.gen::<i32>(), rng.gen::<u32>())
//! }
//! ```
//!
//! ```rust
//! let tuple = rand::random::<(f64, char)>();
//! println!("{:?}", tuple)
//! ```
//!
//! ## Monte Carlo estimation of π
//!
//! For this example, imagine we have a square with sides of length 2 and a unit
//! circle, both centered at the origin. Since the area of a unit circle is π,
//! we have:
//!
//! ```text
//!     (area of unit circle) / (area of square) = π / 4
//! ```
//!
//! So if we sample many points randomly from the square, roughly π / 4 of them
//! should be inside the circle.
//!
//! We can use the above fact to estimate the value of π: pick many points in
//! the square at random, calculate the fraction that fall within the circle,
//! and multiply this fraction by 4.
//!
//! ```
//! use rand::distributions::{Distribution, Range};
//!
//! fn main() {
//!    let between = Range::new(-1f64, 1.);
//!    let mut rng = rand::thread_rng();
//!
//!    let total = 1_000_000;
//!    let mut in_circle = 0;
//!
//!    for _ in 0..total {
//!        let a = between.sample(&mut rng);
//!        let b = between.sample(&mut rng);
//!        if a*a + b*b <= 1. {
//!            in_circle += 1;
//!        }
//!    }
//!
//!    // prints something close to 3.14159...
//!    println!("{}", 4. * (in_circle as f64) / (total as f64));
//! }
//! ```
//!
//! ## Monty Hall Problem
//!
//! This is a simulation of the [Monty Hall Problem][]:
//!
//! > Suppose you're on a game show, and you're given the choice of three doors:
//! > Behind one door is a car; behind the others, goats. You pick a door, say
//! > No. 1, and the host, who knows what's behind the doors, opens another
//! > door, say No. 3, which has a goat. He then says to you, "Do you want to
//! > pick door No. 2?" Is it to your advantage to switch your choice?
//!
//! The rather unintuitive answer is that you will have a 2/3 chance of winning
//! if you switch and a 1/3 chance of winning if you don't, so it's better to
//! switch.
//!
//! This program will simulate the game show and with large enough simulation
//! steps it will indeed confirm that it is better to switch.
//!
//! [Monty Hall Problem]: https://en.wikipedia.org/wiki/Monty_Hall_problem
//!
//! ```
//! use rand::Rng;
//! use rand::distributions::{Distribution, Range};
//!
//! struct SimulationResult {
//!     win: bool,
//!     switch: bool,
//! }
//!
//! // Run a single simulation of the Monty Hall problem.
//! fn simulate<R: Rng>(random_door: &Range<u32>, rng: &mut R)
//!                     -> SimulationResult {
//!     let car = random_door.sample(rng);
//!
//!     // This is our initial choice
//!     let mut choice = random_door.sample(rng);
//!
//!     // The game host opens a door
//!     let open = game_host_open(car, choice, rng);
//!
//!     // Shall we switch?
//!     let switch = rng.gen();
//!     if switch {
//!         choice = switch_door(choice, open);
//!     }
//!
//!     SimulationResult { win: choice == car, switch: switch }
//! }
//!
//! // Returns the door the game host opens given our choice and knowledge of
//! // where the car is. The game host will never open the door with the car.
//! fn game_host_open<R: Rng>(car: u32, choice: u32, rng: &mut R) -> u32 {
//!     let choices = free_doors(&[car, choice]);
//!     rand::seq::sample_slice(rng, &choices, 1)[0]
//! }
//!
//! // Returns the door we switch to, given our current choice and
//! // the open door. There will only be one valid door.
//! fn switch_door(choice: u32, open: u32) -> u32 {
//!     free_doors(&[choice, open])[0]
//! }
//!
//! fn free_doors(blocked: &[u32]) -> Vec<u32> {
//!     (0..3).filter(|x| !blocked.contains(x)).collect()
//! }
//!
//! fn main() {
//!     // The estimation will be more accurate with more simulations
//!     let num_simulations = 10000;
//!
//!     let mut rng = rand::thread_rng();
//!     let random_door = Range::new(0, 3);
//!
//!     let (mut switch_wins, mut switch_losses) = (0, 0);
//!     let (mut keep_wins, mut keep_losses) = (0, 0);
//!
//!     println!("Running {} simulations...", num_simulations);
//!     for _ in 0..num_simulations {
//!         let result = simulate(&random_door, &mut rng);
//!
//!         match (result.win, result.switch) {
//!             (true, true) => switch_wins += 1,
//!             (true, false) => keep_wins += 1,
//!             (false, true) => switch_losses += 1,
//!             (false, false) => keep_losses += 1,
//!         }
//!     }
//!
//!     let total_switches = switch_wins + switch_losses;
//!     let total_keeps = keep_wins + keep_losses;
//!
//!     println!("Switched door {} times with {} wins and {} losses",
//!              total_switches, switch_wins, switch_losses);
//!
//!     println!("Kept our choice {} times with {} wins and {} losses",
//!              total_keeps, keep_wins, keep_losses);
//!
//!     // With a large number of simulations, the values should converge to
//!     // 0.667 and 0.333 respectively.
//!     println!("Estimated chance to win if we switch: {}",
//!              switch_wins as f32 / total_switches as f32);
//!     println!("Estimated chance to win if we don't: {}",
//!              keep_wins as f32 / total_keeps as f32);
//! }
//! ```

#![doc(html_logo_url = "https://www.rust-lang.org/logos/rust-logo-128x128-blk.png",
       html_favicon_url = "https://www.rust-lang.org/favicon.ico",
       html_root_url = "https://docs.rs/rand/0.4")]

#![deny(missing_debug_implementations)]

#![cfg_attr(not(feature="std"), no_std)]
#![cfg_attr(all(feature="alloc", not(feature="std")), feature(alloc))]
#![cfg_attr(feature = "i128_support", feature(i128_type, i128))]

#[cfg(feature="std")] extern crate std as core;
#[cfg(all(feature = "alloc", not(feature="std")))] extern crate alloc;

#[cfg(test)] #[cfg(feature="serde-1")] extern crate bincode;
#[cfg(feature="serde-1")] extern crate serde;
#[cfg(feature="serde-1")] #[macro_use] extern crate serde_derive;

#[cfg(feature = "log")] #[macro_use] extern crate log;
#[cfg(not(feature = "log"))] macro_rules! trace { ($($x:tt)*) => () }
#[cfg(not(feature = "log"))] macro_rules! debug { ($($x:tt)*) => () }
#[cfg(all(feature="std", not(feature = "log")))] macro_rules! info { ($($x:tt)*) => () }
#[cfg(not(feature = "log"))] macro_rules! warn { ($($x:tt)*) => () }
#[cfg(all(feature="std", not(feature = "log")))] macro_rules! error { ($($x:tt)*) => () }


use core::{marker, mem};
#[cfg(feature="std")] use std::cell::RefCell;
#[cfg(feature="std")] use std::rc::Rc;
#[cfg(all(feature="alloc", not(feature="std")))] use alloc::boxed::Box;

// external rngs
pub use jitter::JitterRng;
#[cfg(feature="std")] pub use os::OsRng;

// pseudo rngs
pub use isaac::{IsaacRng, Isaac64Rng};
pub use chacha::ChaChaRng;
pub use prng::XorShiftRng;
pub use prng::Hc128Rng;

// error types
pub use error::{ErrorKind, Error};

// local use declarations
#[cfg(target_pointer_width = "32")]
use prng::IsaacRng as IsaacWordRng;
#[cfg(target_pointer_width = "64")]
use prng::Isaac64Rng as IsaacWordRng;

use distributions::{Distribution, Range};
use distributions::range::SampleRange;
#[cfg(feature="std")] use reseeding::ReseedingRng;

// public modules
pub mod distributions;
mod impls;
pub mod jitter;
#[cfg(feature="std")] pub mod os;
#[cfg(feature="std")] pub mod read;
pub mod reseeding;
#[cfg(any(feature="std", feature = "alloc"))] pub mod seq;

// These tiny modules are here to avoid API breakage, probably only temporarily
pub mod chacha {
    //! The ChaCha random number generator.
    pub use prng::ChaChaRng;
}
pub mod isaac {
    //! The ISAAC random number generator.
    pub use prng::{IsaacRng, Isaac64Rng};
}

// private modules
mod le;
mod error;
mod rand_impls;
mod prng;


/// A type that can be randomly generated using an `Rng`.
///
/// ## Built-in Implementations
///
/// `Rand` is implemented for any type supporting the [`Uniform`] distribution.
/// That includes: floating point numbers.
///
/// This crate implements `Rand` for various primitive types.  Assuming the
/// provided `Rng` is well-behaved, these implementations generate values with
/// the following ranges and distributions:
///
/// * `char`: Uniformly distributed over all Unicode scalar values, i.e. all
///   code points in the range `0...0x10_FFFF`, except for the range
///   `0xD800...0xDFFF` (the surrogate code points).  This includes
///   unassigned/reserved code points.
/// * `bool`: Generates `false` or `true`, each with probability 0.5.
///
/// The following aggregate types also implement `Rand` as long as their
/// component types implement it:
///
/// * Tuples and arrays: Each element of the tuple or array is generated
///   independently, using its own `Rand` implementation.
/// * `Option<T>`: Returns `None` with probability 0.5; otherwise generates a
///   random `T` and returns `Some(T)`.
/// 
/// [`Uniform`]: distributions/struct.Uniform.html
pub trait Rand : Sized {
    /// Generates a random instance of this type using the specified source of
    /// randomness.
    fn rand<R: Rng>(rng: &mut R) -> Self;
}

/// The core of a random number generator.
/// 
/// This trait encapsulates the low-level functionality common to all
/// generators, and is the "back end", to be implemented by generators.
/// End users should normally use [`Rng`] instead.
/// 
/// Unlike [`Rng`], this trait is object-safe. To use a type-erased [`Rng`] —
/// i.e. dynamic dispatch — this trait must be used, along with [`Rng`] to
/// use its generic functions:
/// 
/// ```
/// use rand::{Rng, RngCore};
/// 
/// fn use_rng(mut rng: &mut RngCore) -> u32 {
///     rng.gen_range(1, 7)
/// }
/// 
/// // or:
/// fn use_any_rng<R: RngCore>(rng: &mut R) -> char {
///     // TODO: generating a single char should be easier than this
///     rng.gen_ascii_chars().next().unwrap()
/// }
/// ```
/// 
/// Several extension traits exist:
/// 
/// *   [`Rng`] provides high-level functionality using generic functions
/// *   [`SeedableRng`] is another low-level trait to be implemented by PRNGs
///     (algorithmic RNGs), concerning creation and seeding
/// *   [`NewRng`] is a high-level trait providing a `new()` function, allowing
///     easy construction of freshly-seeded PRNGs
/// 
/// [`Rng`]: trait.Rng.html
/// [`SeedableRng`]: trait.SeedableRng.html
/// [`NewRng`]: trait.NewRng.html
pub trait RngCore {
    /// Return the next random `u32`.
    ///
    /// Implementations of this trait must implement at least one of
    /// `next_u32`, `next_u64` and `fill_bytes` directly. In the case this
    /// function is not implemented directly, it can be implemented using
    /// `self.next_u64() as u32` or via `fill_bytes` (TODO: expose helper
    /// function).
    fn next_u32(&mut self) -> u32;

    /// Return the next random `u64`.
    ///
    /// Implementations of this trait must implement at least one of
    /// `next_u32`, `next_u64` and `fill_bytes` directly. In the case this
    /// function is not implemented directly, the default implementation will
    /// generate values via `next_u32` in little-endian fashion, or this
    /// function can be implemented via `fill_bytes` (TODO: expose helper
    /// function).
    ///
    /// Types wrapping an inner RNG must not use the default implementation,
    /// since the inner RNG's implementation may produce different values.
    fn next_u64(&mut self) -> u64 {
        impls::next_u64_via_u32(self)
    }

    /// Return the next random f32 selected from the half-open
    /// interval `[0, 1)`.
    ///
    /// This uses a technique described by Saito and Matsumoto at
    /// MCQMC'08. Given that the IEEE floating point numbers are
    /// uniformly distributed over [1,2), we generate a number in
    /// this range and then offset it onto the range [0,1). Our
    /// choice of bits (masking v. shifting) is arbitrary and
    /// should be immaterial for high quality generators. For low
    /// quality generators (ex. LCG), prefer bitshifting due to
    /// correlation between sequential low order bits.
    ///
    /// See:
    /// A PRNG specialized in double precision floating point numbers using
    /// an affine transition
    ///
    /// * <http://www.math.sci.hiroshima-u.ac.jp/~m-mat/MT/ARTICLES/dSFMT.pdf>
    /// * <http://www.math.sci.hiroshima-u.ac.jp/~m-mat/MT/SFMT/dSFMT-slide-e.pdf>
    ///
    /// By default this is implemented in terms of `next_u32`, but a
    /// random number generator which can generate numbers satisfying
    /// the requirements directly can overload this for performance.
    /// It is required that the return value lies in `[0, 1)`.
    fn next_f32(&mut self) -> f32 {
        const UPPER_MASK: u32 = 0x3F800000;
        const LOWER_MASK: u32 = 0x7FFFFF;
        let tmp = UPPER_MASK | (self.next_u32() & LOWER_MASK);
        let result: f32 = unsafe { mem::transmute(tmp) };
        result - 1.0
    }

    /// Return the next random f64 selected from the half-open
    /// interval `[0, 1)`.
    ///
    /// By default this is implemented in terms of `next_u64`, but a
    /// random number generator which can generate numbers satisfying
    /// the requirements directly can overload this for performance.
    /// It is required that the return value lies in `[0, 1)`.
    fn next_f64(&mut self) -> f64 {
        const UPPER_MASK: u64 = 0x3FF0000000000000;
        const LOWER_MASK: u64 = 0xFFFFFFFFFFFFF;
        let tmp = UPPER_MASK | (self.next_u64() & LOWER_MASK);
        let result: f64 = unsafe { mem::transmute(tmp) };
        result - 1.0
    }

    /// Fill `dest` with random data.
    ///
    /// Implementations of this trait must implement at least one of
    /// `next_u32`, `next_u64` and `fill_bytes` directly. In the case this
    /// function is not implemented directly, the default implementation will
    /// generate values via `next_u64` in little-endian fashion.
    /// (TODO: expose helper function to allow implementation via `next_u32`.)
    ///
    /// There is no requirement on how this method generates values relative to
    /// `next_u32` or `next_u64`; e.g. a `u64` cast to bytes is not required to
    /// have the same value as eight bytes filled via this function. There *is*
    /// a requirement of portability for reproducible generators which implies
    /// that any seedable generator must fix endianness when generating bytes.
    ///
    /// Types wrapping an inner RNG must not use the default implementation,
    /// since the inner RNG's implementation may produce different values.
    ///
    /// This method should guarantee that `dest` is entirely filled
    /// with new data, and may panic if this is impossible
    /// (e.g. reading past the end of a file that is being used as the
    /// source of randomness).
    ///
    /// # Example
    ///
    /// ```rust
    /// use rand::{thread_rng, RngCore};
    ///
    /// let mut v = [0u8; 13579];
    /// thread_rng().fill_bytes(&mut v);
    /// println!("{:?}", &v[..]);
    /// ```
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        impls::fill_bytes_via_u64(self, dest)
    }

    /// Fill `dest` entirely with random data.
    ///
    /// This is the only method which allows an RNG to report errors while
    /// generating random data; other methods either handle the error
    /// internally or panic. This method is
    /// the intended way to use external (true) RNGs, like `OsRng`. Its main
    /// use-cases are to generate keys and to seed (infallible) PRNGs.
    /// 
    /// Other than error handling, this method is identical to [`fill_bytes`], and
    /// has a default implementation simply wrapping [`fill_bytes`].
    /// 
    /// [`fill_bytes`]: trait.RngCore.html#method.fill_bytes
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        Ok(self.fill_bytes(dest))
    }
}

/// An automatically-implemented extension trait on [`RngCore`] providing high-level
/// generic methods for sampling values and other convenience methods.
/// 
/// This is the primary trait to use when generating random values. Example:
/// 
/// ```
/// use rand::Rng;
/// 
/// fn use_rng<R: Rng>(rng: &mut R) -> f32 {
///     rng.gen()
/// }
/// ```
/// 
/// Since this trait exclusively uses generic methods, it is marked `Sized`.
/// Should it be necessary to support trait objects, use [`RngCore`].
/// Since `Rng` extends `RngCore` and every `RngCore` implements `Rng`, usage
/// of the two traits is somewhat interchangeable.
/// 
/// [`RngCore`]: trait.RngCore.html
pub trait Rng: RngCore + Sized {
    /// Sample a new value, using the given distribution.
    /// 
    /// ### Example
    /// 
    /// ```rust
    /// use rand::{thread_rng, Rng};
    /// use rand::distributions::Range;
    /// 
    /// let mut rng = thread_rng();
    /// let x: i32 = rng.sample(Range::new(10, 15));
    /// ```
    fn sample<T, D: Distribution<T>>(&mut self, distr: D) -> T where Self: Sized {
        distr.sample(self)
    }
    
    /// Return a random value of a `Rand` type.
    ///
    /// # Example
    ///
    /// ```rust
    /// use rand::{thread_rng, Rng};
    ///
    /// let mut rng = thread_rng();
    /// let x: u32 = rng.gen();
    /// println!("{}", x);
    /// println!("{:?}", rng.gen::<(f64, bool)>());
    /// ```
    #[inline(always)]
    fn gen<T: Rand>(&mut self) -> T {
        Rand::rand(self)
    }

    /// Return an iterator that will yield an infinite number of randomly
    /// generated items.
    ///
    /// # Example
    ///
    /// ```
    /// use rand::{thread_rng, Rng};
    ///
    /// let mut rng = thread_rng();
    /// let x = rng.gen_iter::<u32>().take(10).collect::<Vec<u32>>();
    /// println!("{:?}", x);
    /// println!("{:?}", rng.gen_iter::<(f64, bool)>().take(5)
    ///                     .collect::<Vec<(f64, bool)>>());
    /// ```
    fn gen_iter<'a, T: Rand>(&'a mut self) -> Generator<'a, T, Self> {
        Generator { rng: self, _marker: marker::PhantomData }
    }

    /// Generate a random value in the range [`low`, `high`), i.e. inclusive of
    /// `low` and exclusive of `high`.
    ///
    /// This is a convenience wrapper around
    /// `distributions::Range`. If this function will be called
    /// repeatedly with the same arguments, one should use `Range`, as
    /// that will amortize the computations that allow for perfect
    /// uniformity, as they only happen when constructing the `Range`.
    ///
    /// # Panics
    ///
    /// Panics if `low >= high`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use rand::{thread_rng, Rng};
    ///
    /// let mut rng = thread_rng();
    /// let n: u32 = rng.gen_range(0, 10);
    /// println!("{}", n);
    /// let m: f64 = rng.gen_range(-40.0f64, 1.3e5f64);
    /// println!("{}", m);
    /// ```
    fn gen_range<T: PartialOrd + SampleRange>(&mut self, low: T, high: T) -> T {
        assert!(low < high, "Rng::gen_range called with low >= high");
        Range::new(low, high).sample(self)
    }

    /// Return a bool with a 1 in n chance of true
    ///
    /// # Example
    ///
    /// ```rust
    /// use rand::{thread_rng, Rng};
    ///
    /// let mut rng = thread_rng();
    /// println!("{}", rng.gen_weighted_bool(3));
    /// ```
    fn gen_weighted_bool(&mut self, n: u32) -> bool {
        n <= 1 || self.gen_range(0, n) == 0
    }

    /// Return an iterator of random characters from the set A-Z,a-z,0-9.
    ///
    /// # Example
    ///
    /// ```rust
    /// use rand::{thread_rng, Rng};
    ///
    /// let s: String = thread_rng().gen_ascii_chars().take(10).collect();
    /// println!("{}", s);
    /// ```
    fn gen_ascii_chars<'a>(&'a mut self) -> AsciiGenerator<'a, Self> {
        AsciiGenerator { rng: self }
    }

    /// Return a random element from `values`.
    ///
    /// Return `None` if `values` is empty.
    ///
    /// # Example
    ///
    /// ```
    /// use rand::{thread_rng, Rng};
    ///
    /// let choices = [1, 2, 4, 8, 16, 32];
    /// let mut rng = thread_rng();
    /// println!("{:?}", rng.choose(&choices));
    /// assert_eq!(rng.choose(&choices[..0]), None);
    /// ```
    fn choose<'a, T>(&mut self, values: &'a [T]) -> Option<&'a T> {
        if values.is_empty() {
            None
        } else {
            Some(&values[self.gen_range(0, values.len())])
        }
    }

    /// Return a mutable pointer to a random element from `values`.
    ///
    /// Return `None` if `values` is empty.
    fn choose_mut<'a, T>(&mut self, values: &'a mut [T]) -> Option<&'a mut T> {
        if values.is_empty() {
            None
        } else {
            let len = values.len();
            Some(&mut values[self.gen_range(0, len)])
        }
    }

    /// Shuffle a mutable slice in place.
    ///
    /// This applies Durstenfeld's algorithm for the [Fisher–Yates shuffle](https://en.wikipedia.org/wiki/Fisher%E2%80%93Yates_shuffle#The_modern_algorithm)
    /// which produces an unbiased permutation.
    ///
    /// # Example
    ///
    /// ```rust
    /// use rand::{thread_rng, Rng};
    ///
    /// let mut rng = thread_rng();
    /// let mut y = [1, 2, 3];
    /// rng.shuffle(&mut y);
    /// println!("{:?}", y);
    /// rng.shuffle(&mut y);
    /// println!("{:?}", y);
    /// ```
    fn shuffle<T>(&mut self, values: &mut [T]) {
        let mut i = values.len();
        while i >= 2 {
            // invariant: elements with index >= i have been locked in place.
            i -= 1;
            // lock element i in place.
            values.swap(i, self.gen_range(0, i + 1));
        }
    }
}

impl<R: RngCore> Rng for R {}

impl<'a, R: RngCore + ?Sized> RngCore for &'a mut R {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        (**self).next_u32()
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        (**self).next_u64()
    }

    #[inline]
    fn next_f32(&mut self) -> f32 {
        (**self).next_f32()
    }

    #[inline]
    fn next_f64(&mut self) -> f64 {
        (**self).next_f64()
    }

    #[inline]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        (**self).fill_bytes(dest)
    }
    
    #[inline]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        (**self).try_fill_bytes(dest)
    }
}

#[cfg(any(feature="std", feature="alloc"))]
impl<R: RngCore + ?Sized> RngCore for Box<R> {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        (**self).next_u32()
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        (**self).next_u64()
    }

    #[inline]
    fn next_f32(&mut self) -> f32 {
        (**self).next_f32()
    }

    #[inline]
    fn next_f64(&mut self) -> f64 {
        (**self).next_f64()
    }

    #[inline]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        (**self).fill_bytes(dest)
    }
    
    #[inline]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        (**self).try_fill_bytes(dest)
    }
}

/// Iterator which will generate a stream of random items.
///
/// This iterator is created via the [`gen_iter`] method on [`Rng`].
///
/// [`gen_iter`]: trait.Rng.html#method.gen_iter
/// [`Rng`]: trait.Rng.html
#[derive(Debug)]
pub struct Generator<'a, T, R:'a> {
    rng: &'a mut R,
    _marker: marker::PhantomData<fn() -> T>,
}

impl<'a, T: Rand, R: RngCore> Iterator for Generator<'a, T, R> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        Some(self.rng.gen())
    }
}

/// Iterator which will continuously generate random ascii characters.
///
/// This iterator is created via the [`gen_ascii_chars`] method on [`Rng`].
///
/// [`gen_ascii_chars`]: trait.Rng.html#method.gen_ascii_chars
/// [`Rng`]: trait.Rng.html
#[derive(Debug)]
pub struct AsciiGenerator<'a, R:'a> {
    rng: &'a mut R,
}

impl<'a, R: RngCore> Iterator for AsciiGenerator<'a, R> {
    type Item = char;

    fn next(&mut self) -> Option<char> {
        const GEN_ASCII_STR_CHARSET: &'static [u8] =
            b"ABCDEFGHIJKLMNOPQRSTUVWXYZ\
              abcdefghijklmnopqrstuvwxyz\
              0123456789";
        Some(*self.rng.choose(GEN_ASCII_STR_CHARSET).unwrap() as char)
    }
}

/// A random number generator that can be explicitly seeded.
///
/// This trait encapsulates the low-level functionality common to all
/// pseudo-random number generators (PRNGs, or algorithmic generators).
/// 
/// Normally users should use the [`NewRng`] extension trait, excepting when a
/// fixed seed must be used, in which case usage of [`SeedableRng::from_seed`]
/// is recommended.
/// 
/// [`NewRng`]: trait.NewRng.html
/// [`SeedableRng::from_seed`]: #tymethod.from_seed
pub trait SeedableRng: Sized {
    /// Seed type, which is restricted to types mutably-dereferencable as `u8`
    /// arrays (we recommend `[u8; N]` for some `N`).
    ///
    /// It is recommended to seed PRNGs with a seed of at least circa 100 bits,
    /// which means an array of `[u8; 12]` or greater to avoid picking RNGs with
    /// partially overlapping periods.
    ///
    /// For cryptographic RNG's a seed of 256 bits is recommended, `[u8; 32]`.
    type Seed: Sized + Default + AsMut<[u8]>;

    /// Create a new PRNG using the given seed.
    ///
    /// PRNG implementations are allowed to assume that bits in the seed are
    /// well distributed. That means usually that the number of one and zero
    /// bits are about equal, and values like 0, 1 and (size - 1) are unlikely.
    ///
    /// PRNG implementations are recommended to be reproducible. A PRNG seeded
    /// using this function with a fixed seed should produce the same sequence
    /// of output in the future and on different architectures (with for example
    /// different endianness).
    ///
    /// It is however not required that this function yield the same state as a
    /// reference implementation of the PRNG given equivalent seed; if necessary
    /// another constructor can be used.
    fn from_seed(seed: Self::Seed) -> Self;

    /// Create a new PRNG seeded from another `Rng`.
    ///
    /// This is the recommended way to initialize PRNGs with fresh entropy. The
    /// [`NewRng`] trait provides a convenient new method based on `from_rng`.
    /// 
    /// Usage of this method is not recommended when reproducibility is required
    /// since implementing PRNGs are not required to fix Endianness and are
    /// allowed to modify implementations in new releases.
    ///
    /// It is important to use a good source of randomness to initialize the
    /// PRNG. Cryptographic PRNG may be rendered insecure when seeded from a
    /// non-cryptographic PRNG or with insufficient entropy.
    /// Many non-cryptographic PRNGs will show statistical bias in their first
    /// results if their seed numbers are small or if there is a simple pattern
    /// between them.
    ///
    /// Prefer to seed from a strong external entropy source like [`OsRng`] or
    /// from a cryptographic PRNG; if creating a new generator for cryptographic
    /// uses you *must* seed from a strong source.
    ///
    /// Seeding a small PRNG from another small PRNG is possible, but
    /// something to be careful with. An extreme example of how this can go
    /// wrong is seeding an [`XorShiftRng`] from another [`XorShiftRng`], which
    /// will effectively clone the generator. In general seeding from a
    /// generator which is hard to predict is probably okay.
    ///
    /// PRNG implementations are allowed to assume that a good RNG is provided
    /// for seeding, and that it is cryptographically secure when appropriate.
    /// 
    /// [`NewRng`]: trait.NewRng.html
    /// [`OsRng`]: os/struct.OsRng.html
    /// [`XorShiftRng`]: prng/xorshift/struct.XorShiftRng.html
    fn from_rng<R: RngCore>(rng: &mut R) -> Result<Self, Error> {
        let mut seed = Self::Seed::default();
        rng.try_fill_bytes(seed.as_mut())?;
        Ok(Self::from_seed(seed))
    }
}


/// A convenient way to seed new algorithmic generators, otherwise known as
/// pseudo-random number generators (PRNGs).
///
/// This is the recommended way to create PRNGs, unless a deterministic seed is
/// desired (in which case [`SeedableRng::from_seed`] should be used).
///
/// Note: this trait is automatically implemented for any PRNG implementing
/// [`SeedableRng`] and is not intended to be implemented by users.
///
/// ## Example
///
/// ```
/// use rand::{StdRng, Rng, NewRng};
///
/// let mut rng = StdRng::new().unwrap();
/// println!("Random die roll: {}", rng.gen_range(1, 7));
/// ```
///
/// [`SeedableRng`]: trait.SeedableRng.html
/// [`SeedableRng::from_seed`]: trait.SeedableRng.html#tymethod.from_seed
#[cfg(feature="std")]
pub trait NewRng: SeedableRng {
    /// Creates a new instance, automatically seeded with fresh entropy.
    ///
    /// Normally this will use `OsRng`, but if that fails `JitterRng` will be
    /// used instead. Both should be suitable for cryptography. It is possible
    /// that both entropy sources will fail though unlikely.
    fn new() -> Result<Self, Error>;
}

#[cfg(feature="std")]
impl<R: SeedableRng> NewRng for R {
    fn new() -> Result<Self, Error> {
        R::from_rng(&mut EntropyRng::new())
    }
}

/// The standard RNG. This is designed to be efficient on the current
/// platform.
///
/// Reproducibility of output from this generator is not required, thus future
/// library versions may use a different internal generator with different
/// output. Further, this generator may not be portable and can produce
/// different output depending on the architecture. If you require reproducible
/// output, use a named RNG, for example `ChaChaRng`.
#[derive(Clone, Debug)]
pub struct StdRng(IsaacWordRng);

impl RngCore for StdRng {
    fn next_u32(&mut self) -> u32 {
        self.0.next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        self.0.next_u64()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.0.fill_bytes(dest);
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        self.0.try_fill_bytes(dest)
    }
}

impl SeedableRng for StdRng {
    type Seed = <IsaacWordRng as SeedableRng>::Seed;

    fn from_seed(seed: Self::Seed) -> Self {
        StdRng(IsaacWordRng::from_seed(seed))
    }

    fn from_rng<R: Rng>(rng: &mut R) -> Result<Self, Error> {
        IsaacWordRng::from_rng(rng).map(|rng| StdRng(rng))
    }
}

/// Create a weak random number generator with a default algorithm and seed.
///
/// It returns the fastest `Rng` algorithm currently available in Rust without
/// consideration for cryptography or security. If you require a specifically
/// seeded `Rng` for consistency over time you should pick one algorithm and
/// create the `Rng` yourself.
///
/// This will seed the generator with randomness from thread_rng.
#[cfg(feature="std")]
pub fn weak_rng() -> XorShiftRng {
    XorShiftRng::from_rng(&mut thread_rng()).unwrap_or_else(|err|
        panic!("weak_rng failed: {:?}", err))
}


/// The type returned by [`thread_rng`], essentially just a reference to the
/// PRNG in thread-local memory.
/// 
/// [`thread_rng`]: fn.thread_rng.html
#[cfg(feature="std")]
#[derive(Clone, Debug)]
pub struct ThreadRng {
    rng: Rc<RefCell<ReseedingRng<StdRng, EntropyRng>>>,
}

#[cfg(feature="std")]
thread_local!(
    static THREAD_RNG_KEY: Rc<RefCell<ReseedingRng<StdRng, EntropyRng>>> = {
        const THREAD_RNG_RESEED_THRESHOLD: u64 = 32_768;
        let mut entropy_source = EntropyRng::new();
        let r = StdRng::from_rng(&mut entropy_source).unwrap_or_else(|err|
                panic!("could not initialize thread_rng: {}", err));
        let rng = ReseedingRng::new(r,
                                    THREAD_RNG_RESEED_THRESHOLD,
                                    entropy_source);
        Rc::new(RefCell::new(rng))
    }
);

/// Retrieve the lazily-initialized thread-local random number
/// generator, seeded by the system. Intended to be used in method
/// chaining style, e.g. `thread_rng().gen::<i32>()`, or cached locally, e.g.
/// `let mut rng = thread_rng();`.
///
/// `ThreadRng` uses [`ReseedingRng`] wrapping a [`StdRng`] which is reseeded
/// after generating 32KiB of random data. A single instance is cached per
/// thread and the returned `ThreadRng` is a reference to this instance — hence
/// `ThreadRng` is neither `Send` nor `Sync` but is safe to use within a single
/// thread. This RNG is seeded and reseeded via [`EntropyRng`] as required.
/// 
/// Note that the reseeding is done as an extra precaution against entropy
/// leaks and is in theory unnecessary — to predict `thread_rng`'s output, an
/// attacker would have to either determine most of the RNG's seed or internal
/// state, or crack the algorithm used (ISAAC, which has not been proven
/// cryptographically secure, but has no known attack despite a 20-year old
/// challenge).
/// 
/// [`ReseedingRng`]: reseeding/struct.ReseedingRng.html
/// [`StdRng`]: struct.StdRng.html
/// [`EntropyRng`]: struct.EntropyRng.html
#[cfg(feature="std")]
pub fn thread_rng() -> ThreadRng {
    ThreadRng { rng: THREAD_RNG_KEY.with(|t| t.clone()) }
}

#[cfg(feature="std")]
impl RngCore for ThreadRng {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        self.rng.borrow_mut().next_u32()
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        self.rng.borrow_mut().next_u64()
    }

    #[inline]
    fn fill_bytes(&mut self, bytes: &mut [u8]) {
        self.rng.borrow_mut().fill_bytes(bytes)
    }
    
    #[inline]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        self.rng.borrow_mut().try_fill_bytes(dest)
    }
}

/// An RNG provided specifically for seeding PRNGs.
/// 
/// Where possible, `EntropyRng` retrieves random data from the operating
/// system's interface for random numbers ([`OsRng`]); if that fails it will
/// fall back to the [`JitterRng`] entropy collector. In the latter case it will
/// still try to use [`OsRng`] on the next usage.
/// 
/// This is either a little slow ([`OsRng`] requires a system call) or extremely
/// slow ([`JitterRng`] must use significant CPU time to generate sufficient
/// jitter). It is recommended to only use `EntropyRng` to seed a PRNG (as in
/// [`thread_rng`]) or to generate a small key.
///
/// [`OsRng`]: os/struct.OsRng.html
/// [`JitterRng`]: jitter/struct.JitterRng.html
/// [`thread_rng`]: fn.thread_rng.html
#[cfg(feature="std")]
#[derive(Debug)]
pub struct EntropyRng {
    rng: EntropySource,
}

#[cfg(feature="std")]
#[derive(Debug)]
enum EntropySource {
    Os(OsRng),
    Jitter(JitterRng),
    None,
}

#[cfg(feature="std")]
impl EntropyRng {
    /// Create a new `EntropyRng`.
    ///
    /// This method will do no system calls or other initialization routines,
    /// those are done on first use. This is done to make `new` infallible,
    /// and `try_fill_bytes` the only place to report errors.
    pub fn new() -> Self {
        EntropyRng { rng: EntropySource::None }
    }
}

#[cfg(feature="std")]
impl RngCore for EntropyRng {
    fn next_u32(&mut self) -> u32 {
        impls::next_u32_via_fill(self)
    }

    fn next_u64(&mut self) -> u64 {
        impls::next_u64_via_fill(self)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.try_fill_bytes(dest).unwrap_or_else(|err|
                panic!("all entropy sources failed; first error: {}", err))
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        fn try_os_new(dest: &mut [u8]) -> Result<OsRng, Error>
        {
            let mut rng = OsRng::new()?;
            rng.try_fill_bytes(dest)?;
            Ok(rng)
        }

        fn try_jitter_new(dest: &mut [u8]) -> Result<JitterRng, Error>
        {
            let mut rng = JitterRng::new()?;
            rng.try_fill_bytes(dest)?;
            Ok(rng)
        }

        let mut switch_rng = None;
        match self.rng {
            EntropySource::None => {
                let os_rng_result = try_os_new(dest);
                match os_rng_result {
                    Ok(os_rng) => {
                        debug!("EntropyRng: using OsRng");
                        switch_rng = Some(EntropySource::Os(os_rng));
                    }
                    Err(os_rng_error) => {
                        warn!("EntropyRng: OsRng failed [falling back to JitterRng]: {}",
                              os_rng_error);
                        match try_jitter_new(dest) {
                            Ok(jitter_rng) => {
                                debug!("EntropyRng: using JitterRng");
                                switch_rng = Some(EntropySource::Jitter(jitter_rng));
                            }
                            Err(_jitter_error) => {
                                warn!("EntropyRng: JitterRng failed: {}",
                                      _jitter_error);
                                return Err(os_rng_error);
                            }
                        }
                    }
                }
            }
            EntropySource::Os(ref mut rng) => {
                let os_rng_result = rng.try_fill_bytes(dest);
                if let Err(os_rng_error) = os_rng_result {
                    warn!("EntropyRng: OsRng failed [falling back to JitterRng]: {}",
                          os_rng_error);
                    match try_jitter_new(dest) {
                        Ok(jitter_rng) => {
                            debug!("EntropyRng: using JitterRng");
                            switch_rng = Some(EntropySource::Jitter(jitter_rng));
                        }
                        Err(_jitter_error) => {
                            warn!("EntropyRng: JitterRng failed: {}",
                                  _jitter_error);
                            return Err(os_rng_error);
                        }
                    }
                }
            }
            EntropySource::Jitter(ref mut rng) => {
                if let Ok(os_rng) = try_os_new(dest) {
                    debug!("EntropyRng: using OsRng");
                    switch_rng = Some(EntropySource::Os(os_rng));
                } else {
                    return rng.try_fill_bytes(dest); // use JitterRng
                }
            }
        }
        if let Some(rng) = switch_rng {
            self.rng = rng;
        }
        Ok(())
    }
}

/// Generates a random value using the thread-local random number generator.
/// 
/// This is simply a shortcut for `thread_rng().gen()`. See [`thread_rng`] for
/// documentation of the entropy source and [`Rand`] for documentation of
/// distributions and type-specific generation.
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
/// [`thread_rng`]: fn.thread_rng.html
/// [`Rand`]: trait.Rand.html
#[cfg(feature="std")]
#[inline]
pub fn random<T: Rand>() -> T {
    thread_rng().gen()
}

/// DEPRECATED: use `seq::sample_iter` instead.
///
/// Randomly sample up to `amount` elements from a finite iterator.
/// The order of elements in the sample is not random.
///
/// # Example
///
/// ```rust
/// use rand::{thread_rng, sample};
///
/// let mut rng = thread_rng();
/// let sample = sample(&mut rng, 1..100, 5);
/// println!("{:?}", sample);
/// ```
#[cfg(feature="std")]
#[inline(always)]
#[deprecated(since="0.4.0", note="renamed to seq::sample_iter")]
pub fn sample<T, I, R>(rng: &mut R, iterable: I, amount: usize) -> Vec<T>
    where I: IntoIterator<Item=T>,
          R: Rng,
{
    // the legacy sample didn't care whether amount was met
    seq::sample_iter(rng, iterable, amount)
        .unwrap_or_else(|e| e)
}

#[cfg(test)]
mod test {
    use impls;
    #[cfg(feature="std")]
    use super::{random, thread_rng, EntropyRng};
    use super::{RngCore, Rng, SeedableRng, StdRng};
    #[cfg(feature="alloc")]
    use alloc::boxed::Box;

    pub struct TestRng<R> { inner: R }

    impl<R: RngCore> RngCore for TestRng<R> {
        fn next_u32(&mut self) -> u32 {
            self.inner.next_u32()
        }
        fn next_u64(&mut self) -> u64 {
            self.inner.next_u64()
        }
        fn fill_bytes(&mut self, dest: &mut [u8]) {
            self.inner.fill_bytes(dest)
        }
    }

    pub fn rng(seed: u64) -> TestRng<StdRng> {
        // TODO: use from_hashable
        let mut state = seed;
        let mut seed = <StdRng as SeedableRng>::Seed::default();
        for x in seed.iter_mut() {
            // PCG algorithm
            const MUL: u64 = 6364136223846793005;
            const INC: u64 = 11634580027462260723;
            let oldstate = state;
            state = oldstate.wrapping_mul(MUL).wrapping_add(INC);

            let xorshifted = (((oldstate >> 18) ^ oldstate) >> 27) as u32;
            let rot = (oldstate >> 59) as u32;
            *x = xorshifted.rotate_right(rot) as u8;
        }
        TestRng { inner: StdRng::from_seed(seed) }
    }

    struct ConstRng { i: u64 }
    impl RngCore for ConstRng {
        fn next_u32(&mut self) -> u32 { self.i as u32 }
        fn next_u64(&mut self) -> u64 { self.i }

        fn fill_bytes(&mut self, dest: &mut [u8]) {
            impls::fill_bytes_via_u64(self, dest)
        }
    }
    
    #[test]
    #[cfg(feature="std")]
    fn test_entropy() {
        let mut rng = EntropyRng::new();
        rng.next_u32();
    }

    #[test]
    fn test_fill_bytes_default() {
        let mut r = ConstRng { i: 0x11_22_33_44_55_66_77_88 };

        // check every remainder mod 8, both in small and big vectors.
        let lengths = [0, 1, 2, 3, 4, 5, 6, 7,
                       80, 81, 82, 83, 84, 85, 86, 87];
        for &n in lengths.iter() {
            let mut buffer = [0u8; 87];
            let v = &mut buffer[0..n];
            r.fill_bytes(v);

            // use this to get nicer error messages.
            for (i, &byte) in v.iter().enumerate() {
                if byte == 0 {
                    panic!("byte {} of {} is zero", i, n)
                }
            }
        }
    }

    #[test]
    fn test_gen_range() {
        let mut r = rng(101);
        for _ in 0..1000 {
            let a = r.gen_range(-3, 42);
            assert!(a >= -3 && a < 42);
            assert_eq!(r.gen_range(0, 1), 0);
            assert_eq!(r.gen_range(-12, -11), -12);
        }

        for _ in 0..1000 {
            let a = r.gen_range(10, 42);
            assert!(a >= 10 && a < 42);
            assert_eq!(r.gen_range(0, 1), 0);
            assert_eq!(r.gen_range(3_000_000, 3_000_001), 3_000_000);
        }

    }

    #[test]
    #[should_panic]
    fn test_gen_range_panic_int() {
        let mut r = rng(102);
        r.gen_range(5, -2);
    }

    #[test]
    #[should_panic]
    fn test_gen_range_panic_usize() {
        let mut r = rng(103);
        r.gen_range(5, 2);
    }

    #[test]
    fn test_gen_weighted_bool() {
        let mut r = rng(104);
        assert_eq!(r.gen_weighted_bool(0), true);
        assert_eq!(r.gen_weighted_bool(1), true);
    }

    #[test]
    fn test_gen_ascii_str() {
        let mut r = rng(105);
        assert_eq!(r.gen_ascii_chars().take(0).count(), 0);
        assert_eq!(r.gen_ascii_chars().take(10).count(), 10);
        assert_eq!(r.gen_ascii_chars().take(16).count(), 16);
    }

    #[test]
    fn test_gen_vec() {
        let mut r = rng(106);
        assert_eq!(r.gen_iter::<u8>().take(0).count(), 0);
        assert_eq!(r.gen_iter::<u8>().take(10).count(), 10);
        assert_eq!(r.gen_iter::<f64>().take(16).count(), 16);
    }

    #[test]
    fn test_choose() {
        let mut r = rng(107);
        assert_eq!(r.choose(&[1, 1, 1]).map(|&x|x), Some(1));

        let v: &[isize] = &[];
        assert_eq!(r.choose(v), None);
    }

    #[test]
    fn test_shuffle() {
        let mut r = rng(108);
        let empty: &mut [isize] = &mut [];
        r.shuffle(empty);
        let mut one = [1];
        r.shuffle(&mut one);
        let b: &[_] = &[1];
        assert_eq!(one, b);

        let mut two = [1, 2];
        r.shuffle(&mut two);
        assert!(two == [1, 2] || two == [2, 1]);

        let mut x = [1, 1, 1];
        r.shuffle(&mut x);
        let b: &[_] = &[1, 1, 1];
        assert_eq!(x, b);
    }

    #[test]
    #[cfg(feature="std")]
    fn test_thread_rng() {
        let mut r = thread_rng();
        r.gen::<i32>();
        let mut v = [1, 1, 1];
        r.shuffle(&mut v);
        let b: &[_] = &[1, 1, 1];
        assert_eq!(v, b);
        assert_eq!(r.gen_range(0, 1), 0);
    }

    #[test]
    #[cfg(any(feature="std", feature="alloc"))]
    fn test_rng_trait_object() {
        let mut rng = rng(109);
        {
            let mut r = &mut rng as &mut RngCore;
            r.next_u32();
            let r2 = &mut r;
            r2.gen::<i32>();
            let mut v = [1, 1, 1];
            r2.shuffle(&mut v);
            let b: &[_] = &[1, 1, 1];
            assert_eq!(v, b);
            assert_eq!(r2.gen_range(0, 1), 0);
        }
        {
            let mut r = Box::new(rng) as Box<RngCore>;
            r.next_u32();
            r.gen::<i32>();
            let mut v = [1, 1, 1];
            r.shuffle(&mut v);
            let b: &[_] = &[1, 1, 1];
            assert_eq!(v, b);
            assert_eq!(r.gen_range(0, 1), 0);
        }
    }

    #[test]
    #[cfg(feature="std")]
    fn test_random() {
        // not sure how to test this aside from just getting some values
        let _n : usize = random();
        let _f : f32 = random();
        let _o : Option<Option<i8>> = random();
        let _many : ((),
                     (usize,
                      isize,
                      Option<(u32, (bool,))>),
                     (u8, i8, u16, i16, u32, i32, u64, i64),
                     (f32, (f64, (f64,)))) = random();
    }

    #[test]
    #[cfg(target_pointer_width = "32")]
    fn test_stdrng_construction() {
        let seed = [1,0,0,0, 23,0,0,0, 200,1,0,0, 210,30,0,0,
                    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
        let mut rng1 = StdRng::from_seed(seed);
        assert_eq!(rng1.next_u32(), 2869442790);

        let mut rng2 = StdRng::from_rng(&mut rng1).unwrap();
        assert_eq!(rng2.next_u32(), 3094074039);
    }
    #[test]
    #[cfg(target_pointer_width = "64")]
    fn test_stdrng_construction() {
        let seed = [1,0,0,0, 23,0,0,0, 200,1,0,0, 210,30,0,0,
                    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
        let mut rng1 = StdRng::from_seed(seed);
        assert_eq!(rng1.next_u64(), 14964555543728284049);

        let mut rng2 = StdRng::from_rng(&mut rng1).unwrap();
        assert_eq!(rng2.next_u64(), 919595328260451758);
    }
}
