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
//! Rand provides utilities to generate random numbers, to convert them to
//! useful types and distributions, and some randomness-related algorithms.
//!
//! # Basic usage
//!
//! To get you started quickly, the easiest and highest-level way to get
//! a random value is to use [`random()`].
//!
//! ```
//! let x: u8 = rand::random();
//! println!("{}", x);
//!
//! let y = rand::random::<f64>();
//! println!("{}", y);
//!
//! if rand::random() { // generates a boolean
//!     println!("Heads!");
//! }
//! ```
//!
//! This supports generating most common types but is not very flexible, thus
//! you probably want to learn a bit more about the Rand library.
//!
//!
//! # The two-step process to get a random value
//!
//! Generating random values is typically a two-step process:
//!
//! - get some *random data* (an integer or bit/byte sequence) from a random
//!   number generator (RNG);
//! - use some function to transform that *data* into the type of value you want
//!   (this function is an implementation of some *distribution* describing the
//!   kind of value produced).
//!
//! Rand represents the first step with the [`RngCore`] trait and the second
//! step via a combination of the [`Rng`] extension trait and the
//! [`distributions` module].
//! In practice you probably won't use [`RngCore`] directly unless you are
//! implementing a random number generator (RNG).
//!
//! There are many kinds of RNGs, with different trade-offs. You can read more
//! about them in the [`rngs` module] and even more in the [`prng` module],
//! however, often you can just use [`thread_rng()`]. This function
//! automatically initializes an RNG in thread-local memory, then returns a
//! reference to it. It is fast, good quality, and secure (unpredictable).
//!
//! To turn the output of the RNG into something usable, you usually want to use
//! the methods from the [`Rng`] trait. Some of the most useful methods are:
//!
//! - [`gen`] generates a random value appropriate for the type (just like
//!   [`random()`]). For integers this is normally the full representable range
//!   (e.g. from `0u32` to `std::u32::MAX`), for floats this is between 0 and 1,
//!   and some other types are supported, including arrays and tuples. See the
//!   [`Standard`] distribution which provides the implementations.
//! - [`gen_range`] samples from a specific range of values; this is like
//!   [`gen`] but with specific upper and lower bounds.
//! - [`sample`] samples directly from some distribution.
//!
//! [`random()`] is defined using just the above: `thread_rng().gen()`.
//!
//! ## Distributions
//!
//! What are distributions, you ask? Specifying only the type and range of
//! values (known as the *sample space*) is not enough; samples must also have
//! a *probability distribution*, describing the relative probability of
//! sampling each value in that space.
//!
//! In many cases a *uniform* distribution is used, meaning roughly that each
//! value is equally likely (or for "continuous" types like floats, that each
//! equal-sized sub-range has the same probability of containing a sample).
//! [`gen`] and [`gen_range`] both use statistically uniform distributions.
//!
//! The [`distributions` module] provides implementations
//! of some other distributions, including Normal, Log-Normal and Exponential.
//! 
//! It is worth noting that the functionality already mentioned is implemented
//! with distributions: [`gen`] samples values using the [`Standard`]
//! distribution, while [`gen_range`] uses [`Uniform`].
//!
//! ## Importing (prelude)
//!
//! The most convenient way to import items from Rand is to use the [prelude].
//! This includes the most important parts of Rand, but only those unlikely to
//! cause name conflicts.
//!
//! Note that Rand 0.5 has significantly changed the module organization and
//! contents relative to previous versions. Where possible old names have been
//! kept (but are hidden in the documentation), however these will be removed
//! in the future. We therefore recommend migrating to use the prelude or the
//! new module organization in your imports.
//!
//!
//! ## Examples
//!
//! ```
//! use rand::prelude::*;
//!
//! // thread_rng is often the most convenient source of randomness:
//! let mut rng = thread_rng();
//! 
//! if rng.gen() { // random bool
//!     let x: f64 = rng.gen(); // random number in range [0, 1)
//!     println!("x is: {}", x);
//!     let ch = rng.gen::<char>(); // using type annotation
//!     println!("char is: {}", ch);
//!     println!("Number from 0 to 9: {}", rng.gen_range(0, 10));
//! }
//! ```
//!
//!
//! # More functionality
//!
//! The [`Rng`] trait includes a few more methods not mentioned above:
//!
//! - [`Rng::sample_iter`] allows iterating over values from a chosen
//!   distribution.
//! - [`Rng::gen_bool`] generates boolean "events" with a given probability.
//! - [`Rng::fill`] and [`Rng::try_fill`] are fast alternatives to fill a slice
//!   of integers.
//! - [`Rng::shuffle`] randomly shuffles elements in a slice.
//! - [`Rng::choose`] picks one element at random from a slice.
//!
//! For more slice/sequence related functionality, look in the [`seq` module].
//!
//! There is also [`distributions::WeightedChoice`], which can be used to pick
//! elements at random with some probability. But it does not work well at the
//! moment and is going through a redesign.
//!
//!
//! # Error handling
//!
//! Error handling in Rand is a compromise between simplicity and necessity.
//! Most RNGs and sampling functions will never produce errors, and making these
//! able to handle errors would add significant overhead (to code complexity
//! and ergonomics of usage at least, and potentially also performance,
//! depending on the approach).
//! However, external RNGs can fail, and being able to handle this is important.
//!
//! It has therefore been decided that *most* methods should not return a
//! `Result` type, with as exceptions [`Rng::try_fill`],
//! [`RngCore::try_fill_bytes`], and [`SeedableRng::from_rng`].
//!
//! Note that it is the RNG that panics when it fails but is not used through a
//! method that can report errors. Currently Rand contains only three RNGs that
//! can return an error (and thus may panic), and documents this property:
//! [`OsRng`], [`EntropyRng`] and [`ReadRng`]. Other RNGs, like [`ThreadRng`]
//! and [`StdRng`], can be used with all methods without concern.
//!
//! One further problem is that if Rand is unable to get any external randomness
//! when initializing an RNG with [`EntropyRng`], it will panic in
//! [`FromEntropy::from_entropy`], and notably in [`thread_rng()`]. Except by
//! compromising security, this problem is as unsolvable as running out of
//! memory.
//!
//!
//! # Distinction between Rand and `rand_core`
//!
//! The [`rand_core`] crate provides the necessary traits and functionality for
//! implementing RNGs; this includes the [`RngCore`] and [`SeedableRng`] traits
//! and the [`Error`] type.
//! Crates implementing RNGs should depend on [`rand_core`].
//!
//! Applications and libraries consuming random values are encouraged to use the
//! Rand crate, which re-exports the common parts of [`rand_core`].
//!
//!
//! # More examples
//!
//! For some inspiration, see the examples:
//!
//! - [Monte Carlo estimation of π](
//!   https://github.com/rust-lang-nursery/rand/blob/master/examples/monte-carlo.rs)
//! - [Monty Hall Problem](
//!    https://github.com/rust-lang-nursery/rand/blob/master/examples/monty-hall.rs)
//!
//!
//! [`distributions` module]: distributions/index.html
//! [`distributions::WeightedChoice`]: distributions/struct.WeightedChoice.html
//! [`FromEntropy::from_entropy`]: trait.FromEntropy.html#tymethod.from_entropy
//! [`EntropyRng`]: rngs/struct.EntropyRng.html
//! [`Error`]: struct.Error.html
//! [`gen_range`]: trait.Rng.html#method.gen_range
//! [`gen`]: trait.Rng.html#method.gen
//! [`OsRng`]: rngs/struct.OsRng.html
//! [prelude]: prelude/index.html
//! [`rand_core`]: https://crates.io/crates/rand_core
//! [`random()`]: fn.random.html
//! [`ReadRng`]: rngs/adapter/struct.ReadRng.html
//! [`Rng::choose`]: trait.Rng.html#method.choose
//! [`Rng::fill`]: trait.Rng.html#method.fill
//! [`Rng::gen_bool`]: trait.Rng.html#method.gen_bool
//! [`Rng::gen`]: trait.Rng.html#method.gen
//! [`Rng::sample_iter`]: trait.Rng.html#method.sample_iter
//! [`Rng::shuffle`]: trait.Rng.html#method.shuffle
//! [`RngCore`]: trait.RngCore.html
//! [`RngCore::try_fill_bytes`]: trait.RngCore.html#method.try_fill_bytes
//! [`rngs` module]: rngs/index.html
//! [`prng` module]: prng/index.html
//! [`Rng`]: trait.Rng.html
//! [`Rng::try_fill`]: trait.Rng.html#method.try_fill
//! [`sample`]: trait.Rng.html#method.sample
//! [`SeedableRng`]: trait.SeedableRng.html
//! [`SeedableRng::from_rng`]: trait.SeedableRng.html#method.from_rng
//! [`seq` module]: seq/index.html
//! [`SmallRng`]: rngs/struct.SmallRng.html
//! [`StdRng`]: rngs/struct.StdRng.html
//! [`thread_rng()`]: fn.thread_rng.html
//! [`ThreadRng`]: rngs/struct.ThreadRng.html
//! [`Standard`]: distributions/struct.Standard.html
//! [`Uniform`]: distributions/struct.Uniform.html


#![doc(html_logo_url = "https://www.rust-lang.org/logos/rust-logo-128x128-blk.png",
       html_favicon_url = "https://www.rust-lang.org/favicon.ico",
       html_root_url = "https://docs.rs/rand/0.5.6")]

#![deny(missing_docs)]
#![deny(missing_debug_implementations)]
#![doc(test(attr(allow(unused_variables), deny(warnings))))]

#![cfg_attr(not(feature="std"), no_std)]
#![cfg_attr(all(feature="alloc", not(feature="std")), feature(alloc))]
#![cfg_attr(all(feature="i128_support", feature="nightly"), allow(stable_features))] // stable since 2018-03-27
#![cfg_attr(all(feature="i128_support", feature="nightly"), feature(i128_type, i128))]
#![cfg_attr(feature = "stdweb", recursion_limit="128")]

#[cfg(feature="std")] extern crate std as core;
#[cfg(all(feature = "alloc", not(feature="std")))] extern crate alloc;

#[cfg(test)] #[cfg(feature="serde1")] extern crate bincode;
#[cfg(feature="serde1")] extern crate serde;
#[cfg(feature="serde1")] #[macro_use] extern crate serde_derive;

#[cfg(all(target_arch="wasm32", not(target_os="emscripten"), feature="stdweb"))]
#[macro_use]
extern crate stdweb;

extern crate rand_core;

#[cfg(feature = "log")] #[macro_use] extern crate log;
#[allow(unused)]
#[cfg(not(feature = "log"))] macro_rules! trace { ($($x:tt)*) => () }
#[allow(unused)]
#[cfg(not(feature = "log"))] macro_rules! debug { ($($x:tt)*) => () }
#[allow(unused)]
#[cfg(not(feature = "log"))] macro_rules! info { ($($x:tt)*) => () }
#[allow(unused)]
#[cfg(not(feature = "log"))] macro_rules! warn { ($($x:tt)*) => () }
#[allow(unused)]
#[cfg(not(feature = "log"))] macro_rules! error { ($($x:tt)*) => () }


// Re-exports from rand_core
pub use rand_core::{RngCore, CryptoRng, SeedableRng};
pub use rand_core::{ErrorKind, Error};

// Public exports
#[cfg(feature="std")] pub use rngs::thread::thread_rng;

// Public modules
pub mod distributions;
pub mod prelude;
pub mod prng;
pub mod rngs;
#[cfg(feature = "alloc")] pub mod seq;

////////////////////////////////////////////////////////////////////////////////
// Compatibility re-exports. Documentation is hidden; will be removed eventually.

#[cfg(feature="std")] #[doc(hidden)] pub use rngs::adapter::read;
#[doc(hidden)] pub use rngs::adapter::ReseedingRng;

#[allow(deprecated)]
#[cfg(feature="std")] #[doc(hidden)] pub use rngs::EntropyRng;

#[allow(deprecated)]
#[cfg(all(feature="std",
          any(target_os = "linux", target_os = "android",
              target_os = "netbsd",
              target_os = "dragonfly",
              target_os = "haiku",
              target_os = "emscripten",
              target_os = "solaris",
              target_os = "cloudabi",
              target_os = "macos", target_os = "ios",
              target_os = "freebsd",
              target_os = "openbsd", target_os = "bitrig",
              target_os = "redox",
              target_os = "fuchsia",
              windows,
              all(target_arch = "wasm32", feature = "stdweb")
)))]
#[doc(hidden)]
pub use rngs::OsRng;

#[doc(hidden)] pub use prng::{ChaChaRng, IsaacRng, Isaac64Rng, XorShiftRng};
#[doc(hidden)] pub use rngs::StdRng;


#[allow(deprecated)]
#[doc(hidden)]
pub mod jitter {
    pub use rngs::{JitterRng, TimerError};
}
#[allow(deprecated)]
#[cfg(all(feature="std",
          any(target_os = "linux", target_os = "android",
              target_os = "netbsd",
              target_os = "dragonfly",
              target_os = "haiku",
              target_os = "emscripten",
              target_os = "solaris",
              target_os = "cloudabi",
              target_os = "macos", target_os = "ios",
              target_os = "freebsd",
              target_os = "openbsd", target_os = "bitrig",
              target_os = "redox",
              target_os = "fuchsia",
              windows,
              all(target_arch = "wasm32", feature = "stdweb")
)))]
#[doc(hidden)]
pub mod os {
    pub use rngs::OsRng;
}
#[allow(deprecated)]
#[doc(hidden)]
pub mod chacha {
    //! The ChaCha random number generator.
    pub use prng::ChaChaRng;
}
#[doc(hidden)]
pub mod isaac {
    //! The ISAAC random number generator.
    pub use prng::{IsaacRng, Isaac64Rng};
}

#[cfg(feature="std")] #[doc(hidden)] pub use rngs::ThreadRng;

////////////////////////////////////////////////////////////////////////////////


use core::{marker, mem, slice};
use distributions::{Distribution, Standard};
use distributions::uniform::{SampleUniform, UniformSampler};


/// A type that can be randomly generated using an [`Rng`].
/// 
/// This is merely an adapter around the [`Standard`] distribution for
/// convenience and backwards-compatibility.
/// 
/// [`Rng`]: trait.Rng.html
/// [`Standard`]: distributions/struct.Standard.html
#[deprecated(since="0.5.0", note="replaced by distributions::Standard")]
pub trait Rand : Sized {
    /// Generates a random instance of this type using the specified source of
    /// randomness.
    fn rand<R: Rng>(rng: &mut R) -> Self;
}

/// An automatically-implemented extension trait on [`RngCore`] providing high-level
/// generic methods for sampling values and other convenience methods.
/// 
/// This is the primary trait to use when generating random values.
/// 
/// # Generic usage
/// 
/// The basic pattern is `fn foo<R: Rng + ?Sized>(rng: &mut R)`. Some
/// things are worth noting here:
/// 
/// - Since `Rng: RngCore` and every `RngCore` implements `Rng`, it makes no
///   difference whether we use `R: Rng` or `R: RngCore`.
/// - The `+ ?Sized` un-bounding allows functions to be called directly on
///   type-erased references; i.e. `foo(r)` where `r: &mut RngCore`. Without
///   this it would be necessary to write `foo(&mut r)`.
/// 
/// An alternative pattern is possible: `fn foo<R: Rng>(rng: R)`. This has some
/// trade-offs. It allows the argument to be consumed directly without a `&mut`
/// (which is how `from_rng(thread_rng())` works); also it still works directly
/// on references (including type-erased references). Unfortunately within the
/// function `foo` it is not known whether `rng` is a reference type or not,
/// hence many uses of `rng` require an extra reference, either explicitly
/// (`distr.sample(&mut rng)`) or implicitly (`rng.gen()`); one may hope the
/// optimiser can remove redundant references later.
/// 
/// Example:
/// 
/// ```
/// # use rand::thread_rng;
/// use rand::Rng;
/// 
/// fn foo<R: Rng + ?Sized>(rng: &mut R) -> f32 {
///     rng.gen()
/// }
///
/// # let v = foo(&mut thread_rng());
/// ```
/// 
/// [`RngCore`]: trait.RngCore.html
pub trait Rng: RngCore {
    /// Return a random value supporting the [`Standard`] distribution.
    ///
    /// [`Standard`]: distributions/struct.Standard.html
    ///
    /// # Example
    ///
    /// ```
    /// use rand::{thread_rng, Rng};
    ///
    /// let mut rng = thread_rng();
    /// let x: u32 = rng.gen();
    /// println!("{}", x);
    /// println!("{:?}", rng.gen::<(f64, bool)>());
    /// ```
    #[inline]
    fn gen<T>(&mut self) -> T where Standard: Distribution<T> {
        Standard.sample(self)
    }

    /// Generate a random value in the range [`low`, `high`), i.e. inclusive of
    /// `low` and exclusive of `high`.
    ///
    /// This function is optimised for the case that only a single sample is
    /// made from the given range. See also the [`Uniform`] distribution
    /// type which may be faster if sampling from the same range repeatedly.
    ///
    /// # Panics
    ///
    /// Panics if `low >= high`.
    ///
    /// # Example
    ///
    /// ```
    /// use rand::{thread_rng, Rng};
    ///
    /// let mut rng = thread_rng();
    /// let n: u32 = rng.gen_range(0, 10);
    /// println!("{}", n);
    /// let m: f64 = rng.gen_range(-40.0f64, 1.3e5f64);
    /// println!("{}", m);
    /// ```
    ///
    /// [`Uniform`]: distributions/uniform/struct.Uniform.html
    fn gen_range<T: PartialOrd + SampleUniform>(&mut self, low: T, high: T) -> T {
        T::Sampler::sample_single(low, high, self)
    }

    /// Sample a new value, using the given distribution.
    ///
    /// ### Example
    ///
    /// ```
    /// use rand::{thread_rng, Rng};
    /// use rand::distributions::Uniform;
    ///
    /// let mut rng = thread_rng();
    /// let x = rng.sample(Uniform::new(10u32, 15));
    /// // Type annotation requires two types, the type and distribution; the
    /// // distribution can be inferred.
    /// let y = rng.sample::<u16, _>(Uniform::new(10, 15));
    /// ```
    fn sample<T, D: Distribution<T>>(&mut self, distr: D) -> T {
        distr.sample(self)
    }

    /// Create an iterator that generates values using the given distribution.
    ///
    /// # Example
    ///
    /// ```
    /// use rand::{thread_rng, Rng};
    /// use rand::distributions::{Alphanumeric, Uniform, Standard};
    ///
    /// let mut rng = thread_rng();
    ///
    /// // Vec of 16 x f32:
    /// let v: Vec<f32> = thread_rng().sample_iter(&Standard).take(16).collect();
    ///
    /// // String:
    /// let s: String = rng.sample_iter(&Alphanumeric).take(7).collect();
    ///
    /// // Combined values
    /// println!("{:?}", thread_rng().sample_iter(&Standard).take(5)
    ///                              .collect::<Vec<(f64, bool)>>());
    ///
    /// // Dice-rolling:
    /// let die_range = Uniform::new_inclusive(1, 6);
    /// let mut roll_die = rng.sample_iter(&die_range);
    /// while roll_die.next().unwrap() != 6 {
    ///     println!("Not a 6; rolling again!");
    /// }
    /// ```
    fn sample_iter<'a, T, D: Distribution<T>>(&'a mut self, distr: &'a D)
        -> distributions::DistIter<'a, D, Self, T> where Self: Sized
    {
        distr.sample_iter(self)
    }

    /// Fill `dest` entirely with random bytes (uniform value distribution),
    /// where `dest` is any type supporting [`AsByteSliceMut`], namely slices
    /// and arrays over primitive integer types (`i8`, `i16`, `u32`, etc.).
    ///
    /// On big-endian platforms this performs byte-swapping to ensure
    /// portability of results from reproducible generators.
    ///
    /// This uses [`fill_bytes`] internally which may handle some RNG errors
    /// implicitly (e.g. waiting if the OS generator is not ready), but panics
    /// on other errors. See also [`try_fill`] which returns errors.
    ///
    /// # Example
    ///
    /// ```
    /// use rand::{thread_rng, Rng};
    ///
    /// let mut arr = [0i8; 20];
    /// thread_rng().fill(&mut arr[..]);
    /// ```
    ///
    /// [`fill_bytes`]: trait.RngCore.html#method.fill_bytes
    /// [`try_fill`]: trait.Rng.html#method.try_fill
    /// [`AsByteSliceMut`]: trait.AsByteSliceMut.html
    fn fill<T: AsByteSliceMut + ?Sized>(&mut self, dest: &mut T) {
        self.fill_bytes(dest.as_byte_slice_mut());
        dest.to_le();
    }

    /// Fill `dest` entirely with random bytes (uniform value distribution),
    /// where `dest` is any type supporting [`AsByteSliceMut`], namely slices
    /// and arrays over primitive integer types (`i8`, `i16`, `u32`, etc.).
    ///
    /// On big-endian platforms this performs byte-swapping to ensure
    /// portability of results from reproducible generators.
    ///
    /// This uses [`try_fill_bytes`] internally and forwards all RNG errors. In
    /// some cases errors may be resolvable; see [`ErrorKind`] and
    /// documentation for the RNG in use. If you do not plan to handle these
    /// errors you may prefer to use [`fill`].
    ///
    /// # Example
    ///
    /// ```
    /// # use rand::Error;
    /// use rand::{thread_rng, Rng};
    ///
    /// # fn try_inner() -> Result<(), Error> {
    /// let mut arr = [0u64; 4];
    /// thread_rng().try_fill(&mut arr[..])?;
    /// # Ok(())
    /// # }
    ///
    /// # try_inner().unwrap()
    /// ```
    ///
    /// [`ErrorKind`]: enum.ErrorKind.html
    /// [`try_fill_bytes`]: trait.RngCore.html#method.try_fill_bytes
    /// [`fill`]: trait.Rng.html#method.fill
    /// [`AsByteSliceMut`]: trait.AsByteSliceMut.html
    fn try_fill<T: AsByteSliceMut + ?Sized>(&mut self, dest: &mut T) -> Result<(), Error> {
        self.try_fill_bytes(dest.as_byte_slice_mut())?;
        dest.to_le();
        Ok(())
    }

    /// Return a bool with a probability `p` of being true.
    ///
    /// This is a wrapper around [`distributions::Bernoulli`].
    ///
    /// # Example
    ///
    /// ```
    /// use rand::{thread_rng, Rng};
    ///
    /// let mut rng = thread_rng();
    /// println!("{}", rng.gen_bool(1.0 / 3.0));
    /// ```
    ///
    /// # Panics
    ///
    /// If `p` < 0 or `p` > 1.
    ///
    /// [`distributions::Bernoulli`]: distributions/bernoulli/struct.Bernoulli.html
    #[inline]
    fn gen_bool(&mut self, p: f64) -> bool {
        let d = distributions::Bernoulli::new(p);
        self.sample(d)
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
    /// This applies Durstenfeld's algorithm for the [Fisher–Yates shuffle](
    /// https://en.wikipedia.org/wiki/Fisher%E2%80%93Yates_shuffle#The_modern_algorithm)
    /// which produces an unbiased permutation.
    ///
    /// # Example
    ///
    /// ```
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

    /// Return an iterator that will yield an infinite number of randomly
    /// generated items.
    ///
    /// # Example
    ///
    /// ```
    /// # #![allow(deprecated)]
    /// use rand::{thread_rng, Rng};
    ///
    /// let mut rng = thread_rng();
    /// let x = rng.gen_iter::<u32>().take(10).collect::<Vec<u32>>();
    /// println!("{:?}", x);
    /// println!("{:?}", rng.gen_iter::<(f64, bool)>().take(5)
    ///                     .collect::<Vec<(f64, bool)>>());
    /// ```
    #[allow(deprecated)]
    #[deprecated(since="0.5.0", note="use Rng::sample_iter(&Standard) instead")]
    fn gen_iter<T>(&mut self) -> Generator<T, &mut Self> where Standard: Distribution<T> {
        Generator { rng: self, _marker: marker::PhantomData }
    }

    /// Return a bool with a 1 in n chance of true
    ///
    /// # Example
    ///
    /// ```
    /// # #![allow(deprecated)]
    /// use rand::{thread_rng, Rng};
    ///
    /// let mut rng = thread_rng();
    /// assert_eq!(rng.gen_weighted_bool(0), true);
    /// assert_eq!(rng.gen_weighted_bool(1), true);
    /// // Just like `rng.gen::<bool>()` a 50-50% chance, but using a slower
    /// // method with different results.
    /// println!("{}", rng.gen_weighted_bool(2));
    /// // First meaningful use of `gen_weighted_bool`.
    /// println!("{}", rng.gen_weighted_bool(3));
    /// ```
    #[deprecated(since="0.5.0", note="use gen_bool instead")]
    fn gen_weighted_bool(&mut self, n: u32) -> bool {
        // Short-circuit after `n <= 1` to avoid panic in `gen_range`
        n <= 1 || self.gen_range(0, n) == 0
    }

    /// Return an iterator of random characters from the set A-Z,a-z,0-9.
    ///
    /// # Example
    ///
    /// ```
    /// # #![allow(deprecated)]
    /// use rand::{thread_rng, Rng};
    ///
    /// let s: String = thread_rng().gen_ascii_chars().take(10).collect();
    /// println!("{}", s);
    /// ```
    #[allow(deprecated)]
    #[deprecated(since="0.5.0", note="use sample_iter(&Alphanumeric) instead")]
    fn gen_ascii_chars(&mut self) -> AsciiGenerator<&mut Self> {
        AsciiGenerator { rng: self }
    }
}

impl<R: RngCore + ?Sized> Rng for R {}

/// Trait for casting types to byte slices
/// 
/// This is used by the [`fill`] and [`try_fill`] methods.
/// 
/// [`fill`]: trait.Rng.html#method.fill
/// [`try_fill`]: trait.Rng.html#method.try_fill
pub trait AsByteSliceMut {
    /// Return a mutable reference to self as a byte slice
    fn as_byte_slice_mut(&mut self) -> &mut [u8];
    
    /// Call `to_le` on each element (i.e. byte-swap on Big Endian platforms).
    fn to_le(&mut self);
}

impl AsByteSliceMut for [u8] {
    fn as_byte_slice_mut(&mut self) -> &mut [u8] {
        self
    }
    
    fn to_le(&mut self) {}
}

macro_rules! impl_as_byte_slice {
    ($t:ty) => {
        impl AsByteSliceMut for [$t] {
            fn as_byte_slice_mut(&mut self) -> &mut [u8] {
                if self.len() == 0 {
                    unsafe {
                        // must not use null pointer
                        slice::from_raw_parts_mut(0x1 as *mut u8, 0)
                    }
                } else {
                    unsafe {
                        slice::from_raw_parts_mut(&mut self[0]
                            as *mut $t
                            as *mut u8,
                            self.len() * mem::size_of::<$t>()
                        )
                    }
                }
            }
            
            fn to_le(&mut self) {
                for x in self {
                    *x = x.to_le();
                }
            }
        }
    }
}

impl_as_byte_slice!(u16);
impl_as_byte_slice!(u32);
impl_as_byte_slice!(u64);
#[cfg(feature="i128_support")] impl_as_byte_slice!(u128);
impl_as_byte_slice!(usize);
impl_as_byte_slice!(i8);
impl_as_byte_slice!(i16);
impl_as_byte_slice!(i32);
impl_as_byte_slice!(i64);
#[cfg(feature="i128_support")] impl_as_byte_slice!(i128);
impl_as_byte_slice!(isize);

macro_rules! impl_as_byte_slice_arrays {
    ($n:expr,) => {};
    ($n:expr, $N:ident, $($NN:ident,)*) => {
        impl_as_byte_slice_arrays!($n - 1, $($NN,)*);
        
        impl<T> AsByteSliceMut for [T; $n] where [T]: AsByteSliceMut {
            fn as_byte_slice_mut(&mut self) -> &mut [u8] {
                self[..].as_byte_slice_mut()
            }

            fn to_le(&mut self) {
                self[..].to_le()
            }
        }
    };
    (!div $n:expr,) => {};
    (!div $n:expr, $N:ident, $($NN:ident,)*) => {
        impl_as_byte_slice_arrays!(!div $n / 2, $($NN,)*);

        impl<T> AsByteSliceMut for [T; $n] where [T]: AsByteSliceMut {
            fn as_byte_slice_mut(&mut self) -> &mut [u8] {
                self[..].as_byte_slice_mut()
            }
            
            fn to_le(&mut self) {
                self[..].to_le()
            }
        }
    };
}
impl_as_byte_slice_arrays!(32, N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,);
impl_as_byte_slice_arrays!(!div 4096, N,N,N,N,N,N,N,);

/// Iterator which will generate a stream of random items.
///
/// This iterator is created via the [`gen_iter`] method on [`Rng`].
///
/// [`gen_iter`]: trait.Rng.html#method.gen_iter
/// [`Rng`]: trait.Rng.html
#[derive(Debug)]
#[allow(deprecated)]
#[deprecated(since="0.5.0", note="use Rng::sample_iter instead")]
pub struct Generator<T, R: RngCore> {
    rng: R,
    _marker: marker::PhantomData<fn() -> T>,
}

#[allow(deprecated)]
impl<T, R: RngCore> Iterator for Generator<T, R> where Standard: Distribution<T> {
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
#[allow(deprecated)]
#[deprecated(since="0.5.0", note="use distributions::Alphanumeric instead")]
pub struct AsciiGenerator<R: RngCore> {
    rng: R,
}

#[allow(deprecated)]
impl<R: RngCore> Iterator for AsciiGenerator<R> {
    type Item = char;

    fn next(&mut self) -> Option<char> {
        const GEN_ASCII_STR_CHARSET: &[u8] =
            b"ABCDEFGHIJKLMNOPQRSTUVWXYZ\
              abcdefghijklmnopqrstuvwxyz\
              0123456789";
        Some(*self.rng.choose(GEN_ASCII_STR_CHARSET).unwrap() as char)
    }
}


/// A convenience extension to [`SeedableRng`] allowing construction from fresh
/// entropy. This trait is automatically implemented for any PRNG implementing
/// [`SeedableRng`] and is not intended to be implemented by users.
///
/// This is equivalent to using `SeedableRng::from_rng(EntropyRng::new())` then
/// unwrapping the result.
///
/// Since this is convenient and secure, it is the recommended way to create
/// PRNGs, though two alternatives may be considered:
///
/// *   Deterministic creation using [`SeedableRng::from_seed`] with a fixed seed
/// *   Seeding from `thread_rng`: `SeedableRng::from_rng(thread_rng())?`;
///     this will usually be faster and should also be secure, but requires
///     trusting one extra component.
///
/// ## Example
///
/// ```
/// use rand::{Rng, FromEntropy};
/// use rand::rngs::StdRng;
///
/// let mut rng = StdRng::from_entropy();
/// println!("Random die roll: {}", rng.gen_range(1, 7));
/// ```
///
/// [`EntropyRng`]: rngs/struct.EntropyRng.html
/// [`SeedableRng`]: trait.SeedableRng.html
/// [`SeedableRng::from_seed`]: trait.SeedableRng.html#tymethod.from_seed
#[cfg(feature="std")]
pub trait FromEntropy: SeedableRng {
    /// Creates a new instance, automatically seeded with fresh entropy.
    ///
    /// Normally this will use `OsRng`, but if that fails `JitterRng` will be
    /// used instead. Both should be suitable for cryptography. It is possible
    /// that both entropy sources will fail though unlikely; failures would
    /// almost certainly be platform limitations or build issues, i.e. most
    /// applications targetting PC/mobile platforms should not need to worry
    /// about this failing.
    ///
    /// # Panics
    ///
    /// If all entropy sources fail this will panic. If you need to handle
    /// errors, use the following code, equivalent aside from error handling:
    ///
    /// ```
    /// # use rand::Error;
    /// use rand::prelude::*;
    /// use rand::rngs::EntropyRng;
    ///
    /// # fn try_inner() -> Result<(), Error> {
    /// // This uses StdRng, but is valid for any R: SeedableRng
    /// let mut rng = StdRng::from_rng(EntropyRng::new())?;
    ///
    /// println!("random number: {}", rng.gen_range(1, 10));
    /// # Ok(())
    /// # }
    ///
    /// # try_inner().unwrap()
    /// ```
    fn from_entropy() -> Self;
}

#[cfg(feature="std")]
impl<R: SeedableRng> FromEntropy for R {
    fn from_entropy() -> R {
        R::from_rng(EntropyRng::new()).unwrap_or_else(|err|
            panic!("FromEntropy::from_entropy() failed: {}", err))
    }
}


/// DEPRECATED: use [`SmallRng`] instead.
///
/// Create a weak random number generator with a default algorithm and seed.
///
/// It returns the fastest `Rng` algorithm currently available in Rust without
/// consideration for cryptography or security. If you require a specifically
/// seeded `Rng` for consistency over time you should pick one algorithm and
/// create the `Rng` yourself.
///
/// This will seed the generator with randomness from `thread_rng`.
///
/// [`SmallRng`]: rngs/struct.SmallRng.html
#[deprecated(since="0.5.0", note="removed in favor of SmallRng")]
#[cfg(feature="std")]
pub fn weak_rng() -> XorShiftRng {
    XorShiftRng::from_rng(thread_rng()).unwrap_or_else(|err|
        panic!("weak_rng failed: {:?}", err))
}

/// Generates a random value using the thread-local random number generator.
///
/// This is simply a shortcut for `thread_rng().gen()`. See [`thread_rng`] for
/// documentation of the entropy source and [`Standard`] for documentation of
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
/// # #![allow(deprecated)]
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
/// [`Standard`]: distributions/struct.Standard.html
#[cfg(feature="std")]
#[inline]
pub fn random<T>() -> T where Standard: Distribution<T> {
    thread_rng().gen()
}

/// DEPRECATED: use `seq::sample_iter` instead.
///
/// Randomly sample up to `amount` elements from a finite iterator.
/// The order of elements in the sample is not random.
///
/// # Example
///
/// ```
/// # #![allow(deprecated)]
/// use rand::{thread_rng, sample};
///
/// let mut rng = thread_rng();
/// let sample = sample(&mut rng, 1..100, 5);
/// println!("{:?}", sample);
/// ```
#[cfg(feature="std")]
#[inline]
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
    use rngs::mock::StepRng;
    use super::*;
    #[cfg(all(not(feature="std"), feature="alloc"))] use alloc::boxed::Box;

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
        fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
            self.inner.try_fill_bytes(dest)
        }
    }

    pub fn rng(seed: u64) -> TestRng<StdRng> {
        TestRng { inner: StdRng::seed_from_u64(seed) }
    }

    #[test]
    fn test_fill_bytes_default() {
        let mut r = StepRng::new(0x11_22_33_44_55_66_77_88, 0);

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
    fn test_fill() {
        let x = 9041086907909331047;    // a random u64
        let mut rng = StepRng::new(x, 0);
        
        // Convert to byte sequence and back to u64; byte-swap twice if BE.
        let mut array = [0u64; 2];
        rng.fill(&mut array[..]);
        assert_eq!(array, [x, x]);
        assert_eq!(rng.next_u64(), x);
        
        // Convert to bytes then u32 in LE order
        let mut array = [0u32; 2];
        rng.fill(&mut array[..]);
        assert_eq!(array, [x as u32, (x >> 32) as u32]);
        assert_eq!(rng.next_u32(), x as u32);
    }
    
    #[test]
    fn test_fill_empty() {
        let mut array = [0u32; 0];
        let mut rng = StepRng::new(0, 1);
        rng.fill(&mut array);
        rng.fill(&mut array[..]);
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
    #[allow(deprecated)]
    fn test_gen_weighted_bool() {
        let mut r = rng(104);
        assert_eq!(r.gen_weighted_bool(0), true);
        assert_eq!(r.gen_weighted_bool(1), true);
    }

    #[test]
    fn test_gen_bool() {
        let mut r = rng(105);
        for _ in 0..5 {
            assert_eq!(r.gen_bool(0.0), false);
            assert_eq!(r.gen_bool(1.0), true);
        }
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
    fn test_rng_trait_object() {
        use distributions::{Distribution, Standard};
        let mut rng = rng(109);
        let mut r = &mut rng as &mut RngCore;
        r.next_u32();
        r.gen::<i32>();
        let mut v = [1, 1, 1];
        r.shuffle(&mut v);
        let b: &[_] = &[1, 1, 1];
        assert_eq!(v, b);
        assert_eq!(r.gen_range(0, 1), 0);
        let _c: u8 = Standard.sample(&mut r);
    }

    #[test]
    #[cfg(feature="alloc")]
    fn test_rng_boxed_trait() {
        use distributions::{Distribution, Standard};
        let rng = rng(110);
        let mut r = Box::new(rng) as Box<RngCore>;
        r.next_u32();
        r.gen::<i32>();
        let mut v = [1, 1, 1];
        r.shuffle(&mut v);
        let b: &[_] = &[1, 1, 1];
        assert_eq!(v, b);
        assert_eq!(r.gen_range(0, 1), 0);
        let _c: u8 = Standard.sample(&mut r);
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
}
