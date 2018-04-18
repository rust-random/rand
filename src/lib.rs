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
//! ## Example
//! 
//! ```rust
//! // Rng is the main trait and needs to be imported:
//! use rand::{Rng, thread_rng};
//!
//! // thread_rng is often the most convenient source of randomness:
//! let mut rng = thread_rng();
//! if rng.gen() { // random bool
//!     let x: f64 = rng.gen(); // random number in range (0, 1)
//!     println!("x is: {}", x);
//!     println!("Number from 0 to 9: {}", rng.gen_range(0, 10));
//! }
//! ```
//!
//! The key function is [`Rng::gen()`]. It is polymorphic and so can be used to
//! generate many types; the [`Standard`] distribution carries the
//! implementations. In some cases type annotation is required, e.g.
//! `rng.gen::<f64>()`.
//!
//! # Getting random values
//!
//! The most convenient source of randomness is likely [`thread_rng`], which
//! automatically initialises a fast algorithmic generator on first use per
//! thread with thread-local storage.
//! 
//! If one wants to obtain random data directly from an external source it is
//! recommended to use [`EntropyRng`] which manages multiple available sources
//! or [`OsRng`] which retrieves random data directly from the OS. It should be
//! noted that this is significantly slower than using a local generator like
//! [`thread_rng`] and potentially much slower if [`EntropyRng`] must fall back to
//! [`JitterRng`] as a source.
//! 
//! It is also common to use an algorithmic generator in local memory; this may
//! be faster than `thread_rng` and provides more control. In this case
//! [`StdRng`] — the generator behind [`thread_rng`] — and [`SmallRng`] — a
//! small, fast, weak generator — are good choices; more options can be found in
//! the [`prng`] module as well as in other crates.
//! 
//! Local generators need to be seeded. It is recommended to use [`FromEntropy`] or
//! to seed from a strong parent generator with [`from_rng`]:
//! 
//! ```
//! # use rand::{Rng, Error};
//! // seed with fresh entropy:
//! use rand::{StdRng, FromEntropy};
//! let mut rng = StdRng::from_entropy();
//! # let v: u32 = rng.gen();
//! 
//! // seed from thread_rng:
//! use rand::{SmallRng, SeedableRng, thread_rng};
//!
//! # fn try_inner() -> Result<(), Error> {
//! let mut rng = SmallRng::from_rng(thread_rng())?;
//! # let v: u32 = rng.gen();
//! # Ok(())
//! # }
//! # try_inner().unwrap()
//! ```
//! 
//! In case you specifically want to have a reproducible stream of "random"
//! data (e.g. to procedurally generate a game world), select a named algorithm
//! (i.e. not [`StdRng`]/[`SmallRng`] which may be adjusted in the future), and
//! use [`SeedableRng::from_seed`] or a constructor specific to the generator
//! (e.g. [`IsaacRng::new_from_u64`]).
//! 
//! ## Applying / converting random data
//! 
//! The [`RngCore`] trait allows generators to implement a common interface for
//! retrieving random data, but how should you use this? Typically users should
//! use the [`Rng`] trait not [`RngCore`]; this provides more flexible ways to
//! access the same data (e.g. `gen()` can output many more types than
//! `next_u32()` and `next_u64()`; Rust's optimiser should eliminate any
//! overhead). It also provides several useful algorithms,
//! e.g. `gen_bool(p)` to generate events with weighted probability and
//! `shuffle(&mut v[..])` to randomly-order a vector.
//! 
//! The [`distributions`] module provides several more ways to convert random
//! data to useful values, e.g. time of decay is often modelled with an
//! exponential distribution, and the log-normal distribution provides a good
//! model of many natural phenomona.
//! 
//! The [`seq`] module has a few tools applicable to sliceable or iterable data.
//! 
//! ## Cryptographic security
//! 
//! First, lets recap some terminology:
//!
//! - **PRNG:** *Pseudo-Random-Number-Generator* is another name for an
//!   *algorithmic generator*
//! - **CSPRNG:** a *Cryptographically Secure* PRNG
//!
//! Security analysis requires a threat model and expert review; we can provide
//! neither, but we can provide a few hints. We assume that the goal is to
//! produce secret apparently-random data. Therefore, we need:
//! 
//! - A good source of entropy. A known algorithm given known input data is
//!   trivial to predict, and likewise if there's a non-negligable chance that
//!   the input to a PRNG is guessable then there's a chance its output is too.
//!   We recommend seeding CSPRNGs with [`EntropyRng`] or [`OsRng`] which
//!   provide fresh "random" values from an external source.
//!   One can also seed from another CSPRNG, e.g. `thread_rng`, which is faster,
//!   but adds another component which must be trusted.
//! - A strong algorithmic generator. It is possible to use a good entropy
//!   source like `OsRng` directly, and in some cases this is the best option,
//!   but for better performance (or if requiring reproducible values generated
//!   from a fixed seed) it is common to use a local CSPRNG. The basic security
//!   that CSPRNGs must provide is making it infeasible to predict future output
//!   given a sample of past output. A further security that *some* CSPRNGs
//!   provide is *forward secrecy*; this ensures that in the event that the
//!   algorithm's state is revealed, it is infeasible to reconstruct past
//!   output. See the [`CryptoRng`] trait and notes on individual algorithms.
//! - To be careful not to leak secrets like keys and CSPRNG's internal state
//!   and robust against "side channel attacks". This goes well beyond the scope
//!   of random number generation, but this crate takes some precautions:
//!   - to avoid printing CSPRNG state in log files, implementations have a
//!     custom `Debug` implementation which omits all internal state
//!   - `thread_rng` uses [`ReseedingRng`] to periodically refresh its state
//!   - in the future we plan to add some protection against fork attacks
//!     (where the process is forked and each clone generates the same "random"
//!     numbers); this is not yet implemented (see issues #314, #370)
//! 
//! # Examples
//!
//! For some inspiration, see the examples:
//! 
//! *   [Monte Carlo estimation of π](
//!     https://github.com/rust-lang-nursery/rand/blob/master/examples/monte-carlo.rs)
//! *   [Monty Hall Problem](
//!     https://github.com/rust-lang-nursery/rand/blob/master/examples/monty-hall.rs)
//!
//! [`Rng`]: trait.Rng.html
//! [`Rng::gen()`]: trait.Rng.html#method.gen
//! [`RngCore`]: trait.RngCore.html
//! [`FromEntropy`]: trait.FromEntropy.html
//! [`SeedableRng::from_seed`]: trait.SeedableRng.html#tymethod.from_seed
//! [`from_rng`]: trait.SeedableRng.html#method.from_rng
//! [`CryptoRng`]: trait.CryptoRng.html
//! [`thread_rng`]: fn.thread_rng.html
//! [`EntropyRng`]: struct.EntropyRng.html
//! [`OsRng`]: os/struct.OsRng.html
//! [`JitterRng`]: jitter/struct.JitterRng.html
//! [`StdRng`]: struct.StdRng.html
//! [`SmallRng`]: struct.SmallRng.html
//! [`ReseedingRng`]: reseeding/struct.ReseedingRng.html
//! [`prng`]: prng/index.html
//! [`IsaacRng::new_from_u64`]: prng/isaac/struct.IsaacRng.html#method.new_from_u64
//! [`Hc128Rng`]: prng/hc128/struct.Hc128Rng.html
//! [`ChaChaRng`]: prng/chacha/struct.ChaChaRng.html
//! [`IsaacRng`]: prng/isaac/struct.IsaacRng.html
//! [`Isaac64Rng`]: prng/isaac64/struct.Isaac64Rng.html
//! [`seq`]: seq/index.html
//! [`distributions`]: distributions/index.html
//! [`Standard`]: distributions/struct.Standard.html

#![doc(html_logo_url = "https://www.rust-lang.org/logos/rust-logo-128x128-blk.png",
       html_favicon_url = "https://www.rust-lang.org/favicon.ico",
       html_root_url = "https://docs.rs/rand/0.5")]

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

#[cfg(all(target_arch = "wasm32", feature = "stdweb"))]
#[macro_use]
extern crate stdweb;

extern crate rand_core;

#[cfg(feature = "log")] #[macro_use] extern crate log;
#[cfg(not(feature = "log"))] macro_rules! trace { ($($x:tt)*) => () }
#[cfg(not(feature = "log"))] macro_rules! debug { ($($x:tt)*) => () }
#[cfg(all(feature="std", not(feature = "log")))] macro_rules! info { ($($x:tt)*) => () }
#[cfg(not(feature = "log"))] macro_rules! warn { ($($x:tt)*) => () }
#[cfg(all(feature="std", not(feature = "log")))] macro_rules! error { ($($x:tt)*) => () }


// Re-exports from rand_core
pub use rand_core::{RngCore, BlockRngCore, CryptoRng, SeedableRng};
pub use rand_core::{ErrorKind, Error};

// Public exports
#[cfg(feature="std")] pub use entropy_rng::EntropyRng;
#[cfg(feature="std")] pub use os::OsRng;
pub use reseeding::ReseedingRng;
#[cfg(feature="std")] pub use thread_rng::{ThreadRng, thread_rng};
#[cfg(feature="std")] #[allow(deprecated)] pub use thread_rng::random;

// Public modules
pub mod distributions;
pub mod jitter; // Public because of the error type.
pub mod mock;   // Public so we don't export `StepRng` directly, making it a bit
                // more clear it is intended for testing.
pub mod prng;
#[cfg(feature="std")] pub mod read;
#[cfg(feature = "alloc")] pub mod seq;

// These modules are public to avoid API breakage, probably only temporarily.
// Hidden in the documentation.
#[cfg(feature="std")] #[doc(hidden)] pub mod os;
#[doc(hidden)] pub use prng::{ChaChaRng, IsaacRng, Isaac64Rng, XorShiftRng};
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

// private modules
#[cfg(feature="std")] mod entropy_rng;
mod reseeding;
#[cfg(feature="std")] mod thread_rng;


// Normal imports just for this file
use core::{marker, mem, slice};
use distributions::{Distribution, Standard, Uniform};
use distributions::uniform::SampleUniform;
use prng::hc128::Hc128Rng;


/// A type that can be randomly generated using an [`Rng`].
/// 
/// This is merely an adaptor around the [`Standard`] distribution for
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
/// ```rust
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
    /// ```rust
    /// use rand::{thread_rng, Rng};
    ///
    /// let mut rng = thread_rng();
    /// let x: u32 = rng.gen();
    /// println!("{}", x);
    /// println!("{:?}", rng.gen::<(f64, bool)>());
    /// ```
    #[inline(always)]
    fn gen<T>(&mut self) -> T where Standard: Distribution<T> {
        Standard.sample(self)
    }

    /// Generate a random value in the range [`low`, `high`), i.e. inclusive of
    /// `low` and exclusive of `high`.
    ///
    /// This is a convenience wrapper around
    /// `distributions::Uniform::sample_single`. If this function will be called
    /// repeatedly with the same arguments, it will likely be faster to
    /// construct a `Uniform` distribution object and sample from that; this
    /// allows amortization of the computations that allow for perfect
    /// uniformity within the `Uniform::new` constructor.
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
    fn gen_range<T: PartialOrd + SampleUniform>(&mut self, low: T, high: T) -> T {
        Uniform::sample_single(low, high, self)
    }

    /// Sample a new value, using the given distribution.
    ///
    /// ### Example
    ///
    /// ```rust
    /// use rand::{thread_rng, Rng};
    /// use rand::distributions::Uniform;
    ///
    /// let mut rng = thread_rng();
    /// let x: i32 = rng.sample(Uniform::new(10, 15));
    /// ```
    fn sample<T, D: Distribution<T>>(&mut self, distr: D) -> T {
        distr.sample(self)
    }

    /// Create an iterator that generates values using the given distribution.
    ///
    /// # Example
    ///
    /// ```rust
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
    /// ```rust
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
    /// ```rust
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
    /// # Example
    ///
    /// ```rust
    /// use rand::{thread_rng, Rng};
    ///
    /// let mut rng = thread_rng();
    /// println!("{}", rng.gen_bool(1.0 / 3.0));
    /// ```
    ///
    /// # Accuracy note
    ///
    /// `gen_bool` uses 32 bits of the RNG, so if you use it to generate close
    /// to or more than `2^32` results, a tiny bias may become noticable.
    /// A notable consequence of the method used here is that the worst case is
    /// `rng.gen_bool(0.0)`: it has a chance of 1 in `2^32` of being true, while
    /// it should always be false. But using `gen_bool` to consume *many* values
    /// from an RNG just to consistently generate `false` does not match with
    /// the intent of this method.
    fn gen_bool(&mut self, p: f64) -> bool {
        assert!(p >= 0.0 && p <= 1.0);
        // If `p` is constant, this will be evaluated at compile-time.
        let p_int = (p * f64::from(core::u32::MAX)) as u32;
        self.gen::<u32>() <= p_int
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
    /// ```rust
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
    /// ```rust
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
                unsafe {
                    slice::from_raw_parts_mut(&mut self[0]
                        as *mut $t
                        as *mut u8,
                        self.len() * mem::size_of::<$t>()
                    )
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
impl_as_byte_slice_arrays!(32, N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,N,);
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
/// use rand::{StdRng, Rng, FromEntropy};
///
/// let mut rng = StdRng::from_entropy();
/// println!("Random die roll: {}", rng.gen_range(1, 7));
/// ```
///
/// [`EntropyRng`]: struct.EntropyRng.html
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
    /// If all entropy sources fail this will panic. If you need to handle
    /// errors, use the following code, equivalent aside from error handling:
    ///
    /// ```rust
    /// # use rand::Error;
    /// use rand::{Rng, StdRng, EntropyRng, SeedableRng};
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

/// The standard RNG. The PRNG algorithm in `StdRng` is chosen to be efficient
/// on the current platform, to be statistically strong and unpredictable
/// (meaning a cryptographically secure PRNG).
///
/// The current algorithm used on all platforms is [HC-128].
///
/// Reproducibility of output from this generator is however not required, thus
/// future library versions may use a different internal generator with
/// different output. Further, this generator may not be portable and can
/// produce different output depending on the architecture. If you require
/// reproducible output, use a named RNG, for example [`ChaChaRng`].
///
/// [HC-128]: prng/hc128/struct.Hc128Rng.html
/// [`ChaChaRng`]: prng/chacha/struct.ChaChaRng.html
#[derive(Clone, Debug)]
pub struct StdRng(Hc128Rng);

impl RngCore for StdRng {
    #[inline(always)]
    fn next_u32(&mut self) -> u32 {
        self.0.next_u32()
    }

    #[inline(always)]
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
    type Seed = <Hc128Rng as SeedableRng>::Seed;

    fn from_seed(seed: Self::Seed) -> Self {
        StdRng(Hc128Rng::from_seed(seed))
    }

    fn from_rng<R: RngCore>(rng: R) -> Result<Self, Error> {
        Hc128Rng::from_rng(rng).map(StdRng)
    }
}

impl CryptoRng for StdRng {}

/// An RNG recommended when small state, cheap initialization and good
/// performance are required. The PRNG algorithm in `SmallRng` is chosen to be
/// efficient on the current platform, **without consideration for cryptography
/// or security**. The size of its state is much smaller than for [`StdRng`].
///
/// Reproducibility of output from this generator is however not required, thus
/// future library versions may use a different internal generator with
/// different output. Further, this generator may not be portable and can
/// produce different output depending on the architecture. If you require
/// reproducible output, use a named RNG, for example [`XorShiftRng`].
///
/// The current algorithm used on all platforms is [Xorshift].
///
/// # Examples
///
/// Initializing `SmallRng` with a random seed can be done using [`FromEntropy`]:
///
/// ```
/// # use rand::Rng;
/// use rand::{FromEntropy, SmallRng};
///
/// // Create small, cheap to initialize and fast RNG with a random seed.
/// // The randomness is supplied by the operating system.
/// let mut small_rng = SmallRng::from_entropy();
/// # let v: u32 = small_rng.gen();
/// ```
///
/// When initializing a lot of `SmallRng`'s, using [`thread_rng`] can be more
/// efficient:
///
/// ```
/// use std::iter;
/// use rand::{SeedableRng, SmallRng, thread_rng};
///
/// // Create a big, expensive to initialize and slower, but unpredictable RNG.
/// // This is cached and done only once per thread.
/// let mut thread_rng = thread_rng();
/// // Create small, cheap to initialize and fast RNGs with random seeds.
/// // One can generally assume this won't fail.
/// let rngs: Vec<SmallRng> = iter::repeat(())
///     .map(|()| SmallRng::from_rng(&mut thread_rng).unwrap())
///     .take(10)
///     .collect();
/// ```
///
/// [`FromEntropy`]: trait.FromEntropy.html
/// [`StdRng`]: struct.StdRng.html
/// [`thread_rng`]: fn.thread_rng.html
/// [Xorshift]: prng/struct.XorShiftRng.html
/// [`XorShiftRng`]: prng/struct.XorShiftRng.html
#[derive(Clone, Debug)]
pub struct SmallRng(XorShiftRng);

impl RngCore for SmallRng {
    #[inline(always)]
    fn next_u32(&mut self) -> u32 {
        self.0.next_u32()
    }

    #[inline(always)]
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

impl SeedableRng for SmallRng {
    type Seed = <XorShiftRng as SeedableRng>::Seed;

    fn from_seed(seed: Self::Seed) -> Self {
        SmallRng(XorShiftRng::from_seed(seed))
    }

    fn from_rng<R: RngCore>(rng: R) -> Result<Self, Error> {
        XorShiftRng::from_rng(rng).map(SmallRng)
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
/// [`SmallRng`]: struct.SmallRng.html
#[deprecated(since="0.5.0", note="removed in favor of SmallRng")]
#[cfg(feature="std")]
pub fn weak_rng() -> XorShiftRng {
    XorShiftRng::from_rng(thread_rng()).unwrap_or_else(|err|
        panic!("weak_rng failed: {:?}", err))
}

/// DEPRECATED: use `seq::sample_iter` instead.
///
/// Randomly sample up to `amount` elements from a finite iterator.
/// The order of elements in the sample is not random.
///
/// # Example
///
/// ```rust
/// # #![allow(deprecated)]
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
    use mock::StepRng;
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
    fn test_stdrng_construction() {
        let seed = [1,0,0,0, 23,0,0,0, 200,1,0,0, 210,30,0,0,
                    0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
        let mut rng1 = StdRng::from_seed(seed);
        assert_eq!(rng1.next_u64(), 15759097995037006553);

        let mut rng2 = StdRng::from_rng(rng1).unwrap();
        assert_eq!(rng2.next_u64(), 6766915756997287454);
    }
}
