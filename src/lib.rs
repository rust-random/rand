// Copyright 2013-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Utilities for random number generation
//!
//! The `Rng` trait covers random number generation, and can be used directly
//! to produce values of some core types (`u32, u64, f32, f64`, and byte
//! strings). To generate anything else, or to generate values of the above type
//! in generic code, use the `dist` (distributions) module. This includes
//! distributions like ranges, normal and exponential.
//!
//! # Usage
//!
//! This crate is [on crates.io](https://crates.io/crates/rand) and can be
//! used by adding `rand` to the dependencies in your project's `Cargo.toml`.
//!
//! ```toml
//! [dependencies]
//! rand = "0.3"
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
//! in thread-local storage. This RNG can be accessed via `thread_rng`.
//! This RNG is normally randomly seeded
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
//! use rand::dist::uniform;
//!
//! let mut rng = rand::thread_rng();
//! if uniform(&mut rng) { // random bool
//!     let a: i32 = uniform(&mut rng);
//!     let b: u32 = uniform(&mut rng);
//!     println!("i32: {}, u32: {}", a, b)
//! }
//! ```
//!
//! ```rust
//! use rand::thread_rng;
//! use rand::dist::{uniform, uniform01};
//! let mut rng = thread_rng();
//! let tuple: (f64, u8) = (uniform01(&mut rng), uniform(&mut rng));
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
//! use rand::dist::{Sample, Range};
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
//! [Monty Hall Problem]: http://en.wikipedia.org/wiki/Monty_Hall_problem
//!
//! ```
//! use rand::Rng;
//! use rand::dist::{Sample, Range, uniform};
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
//!     let switch = uniform(rng);
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
//!     rand::sample(rng, choices.into_iter(), 1)[0]
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
       html_root_url = "https://docs.rs/rand/0.3")]

#![deny(missing_debug_implementations)]

#![cfg_attr(feature = "i128_support", feature(i128_type))]


use std::cell::RefCell;
use std::mem;
use std::io;
use std::rc::Rc;

pub use read::ReadRng;
pub use os::OsRng;

use dist::{Range, Sample};
use dist::range::SampleRange;

use prng::IsaacWordRng;
use prng::XorShiftRng;

pub mod dist;
pub mod prng;
pub mod reseeding;

mod read;
mod os;

/// A type that can be randomly generated using an `Rng`.
///
/// ## Built-in Implementations
///
/// This crate implements `Rand` for various primitive types.  Assuming the
/// provided `Rng` is well-behaved, these implementations generate values with
/// the following ranges and distributions:
///
/// * Integers (`i32`, `u32`, `isize`, `usize`, etc.): Uniformly distributed
///   over all values of the type.
/// * `char`: Uniformly distributed over all Unicode scalar values, i.e. all
///   code points in the range `0...0x10_FFFF`, except for the range
///   `0xD800...0xDFFF` (the surrogate code points).  This includes
///   unassigned/reserved code points.
/// * `bool`: Generates `false` or `true`, each with probability 0.5.
/// * Floating point types (`f32` and `f64`): Uniformly distributed in the
///   half-open range `[0, 1)`.  (The [`Open01`], [`Closed01`], [`Exp1`], and
///   [`StandardNormal`] wrapper types produce floating point numbers with
///   alternative ranges or distributions.)
///
/// [`Open01`]: struct.Open01.html
/// [`Closed01`]: struct.Closed01.html
/// [`Exp1`]: struct.Exp1.html
/// [`StandardNormal`]: struct.StandardNormal.html
///
/// The following aggregate types also implement `Rand` as long as their
/// component types implement it:
///
/// * Tuples and arrays: Each element of the tuple or array is generated
///   independently, using its own `Rand` implementation.
/// * `Option<T>`: Returns `None` with probability 0.5; otherwise generates a
///   random `T` and returns `Some(T)`.

pub trait Rand : Sized {
    /// Generates a random instance of this type using the specified source of
    /// randomness.
    fn rand<R: Rng>(rng: &mut R) -> Self;
}

/// A random number generator.
pub trait Rng {
    /// Return the next random u32.
    ///
    /// This rarely needs to be called directly, prefer `r.gen()` to
    /// `r.next_u32()`.
    // FIXME #rust-lang/rfcs#628: Should be implemented in terms of next_u64
    fn next_u32(&mut self) -> u32;

    /// Return the next random u64.
    ///
    /// By default this is implemented in terms of `next_u32`. An
    /// implementation of this trait must provide at least one of
    /// these two methods. Similarly to `next_u32`, this rarely needs
    /// to be called directly, prefer `r.gen()` to `r.next_u64()`.
    fn next_u64(&mut self) -> u64 {
        ((self.next_u32() as u64) << 32) | (self.next_u32() as u64)
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
    /// http://www.math.sci.hiroshima-u.ac.jp/~m-mat/MT/ARTICLES/dSFMT.pdf
    /// http://www.math.sci.hiroshima-u.ac.jp/~m-mat/MT/SFMT/dSFMT-slide-e.pdf
    ///
    /// By default this is implemented in terms of `next_u32`, but a
    /// random number generator which can generate numbers satisfying
    /// the requirements directly can overload this for performance.
    /// It is required that the return value lies in `[0, 1)`.
    ///
    /// See `closed01` for the closed interval `[0,1]`, and
    /// `open01` for the open interval `(0,1)`.
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
    ///
    /// See `closed01` for the closed interval `[0,1]`, and
    /// `open01` for the open interval `(0,1)`.
    fn next_f64(&mut self) -> f64 {
        const UPPER_MASK: u64 = 0x3FF0000000000000;
        const LOWER_MASK: u64 = 0xFFFFFFFFFFFFF;
        let tmp = UPPER_MASK | (self.next_u64() & LOWER_MASK);
        let result: f64 = unsafe { mem::transmute(tmp) };
        result - 1.0
    }

    /// Fill `dest` with random data.
    ///
    /// This has a default implementation in terms of `next_u64` and
    /// `next_u32`, but should be overridden by implementations that
    /// offer a more efficient solution than just calling those
    /// methods repeatedly.
    ///
    /// This method does *not* have a requirement to bear any fixed
    /// relationship to the other methods, for example, it does *not*
    /// have to result in the same output as progressively filling
    /// `dest` with `self.gen::<u8>()`, and any such behaviour should
    /// not be relied upon.
    ///
    /// This method should guarantee that `dest` is entirely filled
    /// with new data, and may panic if this is impossible
    /// (e.g. reading past the end of a file that is being used as the
    /// source of randomness).
    ///
    /// # Example
    ///
    /// ```rust
    /// use rand::{thread_rng, Rng};
    ///
    /// let mut v = [0u8; 13579];
    /// thread_rng().fill_bytes(&mut v);
    /// println!("{:?}", &v[..]);
    /// ```
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        // this could, in theory, be done by transmuting dest to a
        // [u64], but this is (1) likely to be undefined behaviour for
        // LLVM, (2) has to be very careful about alignment concerns,
        // (3) adds more `unsafe` that needs to be checked, (4)
        // probably doesn't give much performance gain if
        // optimisations are on.
        let mut count = 0;
        let mut num = 0;
        for byte in dest.iter_mut() {
            if count == 0 {
                // we could micro-optimise here by generating a u32 if
                // we only need a few more bytes to fill the vector
                // (i.e. at most 4).
                num = self.next_u64();
                count = 8;
            }

            *byte = (num & 0xff) as u8;
            num >>= 8;
            count -= 1;
        }
    }

    /// Return a random value of a `Rand` type.
    ///
    /// # Example
    ///
    /// ```rust
    /// use rand::{thread_rng, Rng};
    /// use rand::dist::{uniform, uniform01};
    ///
    /// let mut rng = thread_rng();
    /// let x: u32 = uniform(&mut rng);
    /// let y: f64 = uniform01(&mut rng);
    /// let z: bool = uniform(&mut rng);
    /// println!("{}", x);
    /// println!("{}", y);
    /// println!("{}", z);
    /// ```
    #[inline(always)]
    fn gen<T: Rand>(&mut self) -> T where Self: Sized {
        Rand::rand(self)
    }

    /// Yield an iterator applying some function to self.
    /// 
    /// Unfortunately this is only possible with static dispatch (i.e. where
    /// `Self: Sized`). [Why? Because the method must be generic, to support
    /// the lifetime bound on the `&mut Rng` field of the returned object, if
    /// not also for types `T` and `F`; representing this field requires that
    /// `Rng` trait objects can be constructed, but trait objects cannot be
    /// constructed for traits with generic methods without a `Sized` bound.
    /// But the starting point was wanting a dynamic version of this method,
    /// i.e. not requiring the `Sized` bound.
    /// See `rustc --explain E0038` for more.]
    /// 
    /// # Example
    ///
    /// ```
    /// use rand::{thread_rng, Rng};
    /// use rand::dist::uniform;
    ///
    /// let mut rng = thread_rng();
    /// let x = rng.iter_map(|rng| uniform(rng)).take(10).collect::<Vec<u32>>();
    /// println!("{:?}", x);
    /// ```
    fn iter_map<'a, T, F>(&'a mut self, f: F) -> RngIterator<'a, Self, T, F>
        where Self: Sized, F: Fn(&mut Self) -> T
    {
        RngIterator { rng: self, f: f }
    }

    /// Generate a random value in the range [`low`, `high`).
    ///
    /// This is a convenience wrapper around
    /// `dist::Range`. If this function will be called
    /// repeatedly with the same arguments, one should use `Range`, as
    /// that will amortize the computations that allow for perfect
    /// uniformity, as they only happen on initialization.
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
    fn gen_range<T: PartialOrd + SampleRange>(&mut self, low: T, high: T) -> T where Self: Sized {
        assert!(low < high, "Rng.gen_range called with low >= high");
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
    fn gen_weighted_bool(&mut self, n: u32) -> bool where Self: Sized {
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
    fn gen_ascii_chars<'a>(&'a mut self) -> AsciiGenerator<'a, Self> where Self: Sized {
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
    fn choose<'a, T>(&mut self, values: &'a [T]) -> Option<&'a T> where Self: Sized {
        if values.is_empty() {
            None
        } else {
            Some(&values[self.gen_range(0, values.len())])
        }
    }

    /// Return a mutable pointer to a random element from `values`.
    ///
    /// Return `None` if `values` is empty.
    fn choose_mut<'a, T>(&mut self, values: &'a mut [T]) -> Option<&'a mut T> where Self: Sized {
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
    fn shuffle<T>(&mut self, values: &mut [T]) where Self: Sized {
        let mut i = values.len();
        while i >= 2 {
            // invariant: elements with index >= i have been locked in place.
            i -= 1;
            // lock element i in place.
            values.swap(i, self.gen_range(0, i + 1));
        }
    }
}

impl<'a, R: ?Sized> Rng for &'a mut R where R: Rng {
    fn next_u32(&mut self) -> u32 {
        (**self).next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        (**self).next_u64()
    }

    fn next_f32(&mut self) -> f32 {
        (**self).next_f32()
    }

    fn next_f64(&mut self) -> f64 {
        (**self).next_f64()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        (**self).fill_bytes(dest)
    }
}

impl<R: ?Sized> Rng for Box<R> where R: Rng {
    fn next_u32(&mut self) -> u32 {
        (**self).next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        (**self).next_u64()
    }

    fn next_f32(&mut self) -> f32 {
        (**self).next_f32()
    }

    fn next_f64(&mut self) -> f64 {
        (**self).next_f64()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        (**self).fill_bytes(dest)
    }
}

/// Pseudo-Iterator encapsulating a random number generator.
/// See [`Rng::iter`](trait.Rng.html#method.iter).
/// 
/// This only implements a [`map`](struct.RngIterator.html#method.map) method.
#[derive(Debug)]
pub struct RngIterator<'a, R:'a, T, F: Fn(&mut R) -> T> {
    rng: &'a mut R,
    f: F
}

impl<'a, R:'a, T, F: Fn(&mut R) -> T> Iterator for RngIterator<'a, R, T, F> {
    type Item = T;
    
    fn next(&mut self) -> Option<T> {
        Some((self.f)(self.rng))
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

impl<'a, R: Rng> Iterator for AsciiGenerator<'a, R> {
    type Item = char;

    fn next(&mut self) -> Option<char> {
        const GEN_ASCII_STR_CHARSET: &'static [u8] =
            b"ABCDEFGHIJKLMNOPQRSTUVWXYZ\
              abcdefghijklmnopqrstuvwxyz\
              0123456789";
        Some(*self.rng.choose(GEN_ASCII_STR_CHARSET).unwrap() as char)
    }
}

/// A random number generator that can be explicitly seeded to produce
/// the same stream of randomness multiple times.
pub trait SeedableRng<Seed>: Rng {
    /// Reseed an RNG with the given seed.
    ///
    /// # Example
    ///
    /// ```rust
    /// use rand::{Rng, SeedableRng};
    /// use rand::prng::IsaacWordRng;
    /// use rand::dist::uniform01;
    ///
    /// let seed: &[_] = &[1, 2, 3, 4];
    /// let mut rng: IsaacWordRng = SeedableRng::from_seed(seed);
    /// println!("{}", uniform01::<f64, _>(&mut rng));
    /// rng.reseed(&[5, 6, 7, 8]);
    /// println!("{}", uniform01::<f64, _>(&mut rng));
    /// ```
    fn reseed(&mut self, Seed);

    /// Create a new RNG with the given seed.
    ///
    /// # Example
    ///
    /// ```rust
    /// use rand::{Rng, SeedableRng};
    /// use rand::prng::ChaChaRng;
    /// use rand::dist::uniform01;
    ///
    /// let seed: &[_] = &[1, 2, 3, 4];
    /// let mut rng: ChaChaRng = SeedableRng::from_seed(seed);
    /// println!("{}", uniform01::<f64, _>(&mut rng));
    /// ```
    fn from_seed(seed: Seed) -> Self;
}

/// The standard RNG. This is designed to be efficient on the current
/// platform.
#[derive(Copy, Clone, Debug)]
pub struct StdRng {
    rng: IsaacWordRng,
}

impl StdRng {
    /// Create a randomly seeded instance of `StdRng`.
    ///
    /// This is a very expensive operation as it has to read
    /// randomness from the operating system and use this in an
    /// expensive seeding operation. If one is only generating a small
    /// number of random numbers, or doesn't need the utmost speed for
    /// generating each number, `thread_rng` and/or `random` may be more
    /// appropriate.
    ///
    /// Reading the randomness from the OS may fail, and any error is
    /// propagated via the `io::Result` return value.
    pub fn new() -> io::Result<StdRng> {
        OsRng::new().map(|mut r| StdRng { rng: r.gen() })
    }
}

impl Rng for StdRng {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        self.rng.next_u32()
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        self.rng.next_u64()
    }
}

impl<'a> SeedableRng<&'a [usize]> for StdRng {
    fn reseed(&mut self, seed: &'a [usize]) {
        // the internal RNG can just be seeded from the above
        // randomness.
        self.rng.reseed(unsafe {mem::transmute(seed)})
    }

    fn from_seed(seed: &'a [usize]) -> StdRng {
        StdRng { rng: SeedableRng::from_seed(unsafe {mem::transmute(seed)}) }
    }
}

/// Create a weak random number generator with a default algorithm and seed.
///
/// It returns the fastest `Rng` algorithm currently available in Rust without
/// consideration for cryptography or security. If you require a specifically
/// seeded `Rng` for consistency over time you should pick one algorithm and
/// create the `Rng` yourself.
///
/// This will read randomness from the operating system to seed the
/// generator.
pub fn weak_rng() -> XorShiftRng {
    match OsRng::new() {
        Ok(mut r) => r.gen(),
        Err(e) => panic!("weak_rng: failed to create seeded RNG: {:?}", e)
    }
}

/// Controls how the thread-local RNG is reseeded.
#[derive(Debug)]
struct ThreadRngReseeder;

impl reseeding::Reseeder<StdRng> for ThreadRngReseeder {
    fn reseed(&mut self, rng: &mut StdRng) {
        *rng = match StdRng::new() {
            Ok(r) => r,
            Err(e) => panic!("could not reseed thread_rng: {}", e)
        }
    }
}
const THREAD_RNG_RESEED_THRESHOLD: u64 = 32_768;
type ThreadRngInner = reseeding::ReseedingRng<StdRng, ThreadRngReseeder>;

/// The thread-local RNG.
#[derive(Clone, Debug)]
pub struct ThreadRng {
    rng: Rc<RefCell<ThreadRngInner>>,
}

/// Retrieve the lazily-initialized thread-local random number
/// generator, seeded by the system. Intended to be used in method
/// chaining style, e.g. `thread_rng().gen::<i32>()`.
///
/// The RNG provided will reseed itself from the operating system
/// after generating a certain amount of randomness.
///
/// The internal RNG used is platform and architecture dependent, even
/// if the operating system random number generator is rigged to give
/// the same sequence always. If absolute consistency is required,
/// explicitly select an RNG, e.g. `IsaacRng` or `Isaac64Rng`.
pub fn thread_rng() -> ThreadRng {
    // used to make space in TLS for a random number generator
    thread_local!(static THREAD_RNG_KEY: Rc<RefCell<ThreadRngInner>> = {
        let r = match StdRng::new() {
            Ok(r) => r,
            Err(e) => panic!("could not initialize thread_rng: {}", e)
        };
        let rng = reseeding::ReseedingRng::new(r,
                                               THREAD_RNG_RESEED_THRESHOLD,
                                               ThreadRngReseeder);
        Rc::new(RefCell::new(rng))
    });

    ThreadRng { rng: THREAD_RNG_KEY.with(|t| t.clone()) }
}

impl Rng for ThreadRng {
    fn next_u32(&mut self) -> u32 {
        self.rng.borrow_mut().next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        self.rng.borrow_mut().next_u64()
    }

    #[inline]
    fn fill_bytes(&mut self, bytes: &mut [u8]) {
        self.rng.borrow_mut().fill_bytes(bytes)
    }
}

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
pub fn sample<T, I, R>(rng: &mut R, iterable: I, amount: usize) -> Vec<T>
    where I: IntoIterator<Item=T>,
          R: Rng,
{
    let mut iter = iterable.into_iter();
    let mut reservoir: Vec<T> = iter.by_ref().take(amount).collect();
    // continue unless the iterator was exhausted
    if reservoir.len() == amount {
        for (i, elem) in iter.enumerate() {
            let k = rng.gen_range(0, i + 1 + amount);
            if let Some(spot) = reservoir.get_mut(k) {
                *spot = elem;
            }
        }
    }
    reservoir
}

#[cfg(test)]
mod test {
    use {Rng, thread_rng, SeedableRng, StdRng, sample};
    use dist::{uniform, uniform01};
    use std::iter::repeat;

    pub struct MyRng<R> { inner: R }

    impl<R: Rng> Rng for MyRng<R> {
        fn next_u32(&mut self) -> u32 {
            fn next<T: Rng>(t: &mut T) -> u32 {
                t.next_u32()
            }
            next(&mut self.inner)
        }
    }

    pub fn rng() -> MyRng<::ThreadRng> {
        MyRng { inner: ::thread_rng() }
    }

    struct ConstRng { i: u64 }
    impl Rng for ConstRng {
        fn next_u32(&mut self) -> u32 { self.i as u32 }
        fn next_u64(&mut self) -> u64 { self.i }

        // no fill_bytes on purpose
    }

    pub fn iter_eq<I, J>(i: I, j: J) -> bool
        where I: IntoIterator,
              J: IntoIterator<Item=I::Item>,
              I::Item: Eq
    {
        // make sure the iterators have equal length
        let mut i = i.into_iter();
        let mut j = j.into_iter();
        loop {
            match (i.next(), j.next()) {
                (Some(ref ei), Some(ref ej)) if ei == ej => { }
                (None, None) => return true,
                _ => return false,
            }
        }
    }

    #[test]
    fn test_fill_bytes_default() {
        let mut r = ConstRng { i: 0x11_22_33_44_55_66_77_88 };

        // check every remainder mod 8, both in small and big vectors.
        let lengths = [0, 1, 2, 3, 4, 5, 6, 7,
                       80, 81, 82, 83, 84, 85, 86, 87];
        for &n in lengths.iter() {
            let mut v = repeat(0u8).take(n).collect::<Vec<_>>();
            r.fill_bytes(&mut v);

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
        let mut r = thread_rng();
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
        let mut r = thread_rng();
        r.gen_range(5, -2);
    }

    #[test]
    #[should_panic]
    fn test_gen_range_panic_usize() {
        let mut r = thread_rng();
        r.gen_range(5, 2);
    }

    #[test]
    fn test_gen_weighted_bool() {
        let mut r = thread_rng();
        assert_eq!(r.gen_weighted_bool(0), true);
        assert_eq!(r.gen_weighted_bool(1), true);
    }

    #[test]
    fn test_gen_ascii_str() {
        let mut r = thread_rng();
        assert_eq!(r.gen_ascii_chars().take(0).count(), 0);
        assert_eq!(r.gen_ascii_chars().take(10).count(), 10);
        assert_eq!(r.gen_ascii_chars().take(16).count(), 16);
    }

    #[test]
    fn test_gen_vec() {
        let mut r = thread_rng();
        assert_eq!(r.iter_map(|rng| rng.next_u32()).take(0).count(), 0);
        assert_eq!(r.iter_map(|rng| uniform::<u8, _>(rng)).take(10).count(), 10);
        assert_eq!(r.iter_map(|rng| uniform01::<f64, _>(rng)).take(16).count(), 16);
    }

    #[test]
    fn test_choose() {
        let mut r = thread_rng();
        assert_eq!(r.choose(&[1, 1, 1]).map(|&x|x), Some(1));

        let v: &[isize] = &[];
        assert_eq!(r.choose(v), None);
    }

    #[test]
    fn test_shuffle() {
        let mut r = thread_rng();
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
    fn test_thread_rng() {
        let mut r = thread_rng();
        uniform::<i32, _>(&mut r);
        let mut v = [1, 1, 1];
        r.shuffle(&mut v);
        let b: &[_] = &[1, 1, 1];
        assert_eq!(v, b);
        assert_eq!(r.gen_range(0, 1), 0);
    }

    #[test]
    fn test_rng_trait_object() {
        let mut rng = thread_rng();
        {
            let mut r = &mut rng as &mut Rng;
            r.next_u32();
            uniform::<i32, _>(&mut r);
            let mut v = [1, 1, 1];
            (&mut r).shuffle(&mut v);
            let b: &[_] = &[1, 1, 1];
            assert_eq!(v, b);
            assert_eq!((&mut r).gen_range(0, 1), 0);
        }
        {
            let mut r = Box::new(rng) as Box<Rng>;
            r.next_u32();
            uniform::<i32, _>(&mut r);
            let mut v = [1, 1, 1];
            r.shuffle(&mut v);
            let b: &[_] = &[1, 1, 1];
            assert_eq!(v, b);
            assert_eq!(r.gen_range(0, 1), 0);
        }
    }

    #[test]
    fn test_sample() {
        let min_val = 1;
        let max_val = 100;

        let mut r = thread_rng();
        let vals = (min_val..max_val).collect::<Vec<i32>>();
        let small_sample = sample(&mut r, vals.iter(), 5);
        let large_sample = sample(&mut r, vals.iter(), vals.len() + 5);

        assert_eq!(small_sample.len(), 5);
        assert_eq!(large_sample.len(), vals.len());

        assert!(small_sample.iter().all(|e| {
            **e >= min_val && **e <= max_val
        }));
    }

    #[test]
    fn test_std_rng_seeded() {
        let s = thread_rng().iter_map(|rng| uniform(rng)).take(256).collect::<Vec<usize>>();
        let mut ra: StdRng = SeedableRng::from_seed(&s[..]);
        let mut rb: StdRng = SeedableRng::from_seed(&s[..]);
        assert!(iter_eq(ra.gen_ascii_chars().take(100),
                        rb.gen_ascii_chars().take(100)));
    }

    #[test]
    fn test_std_rng_reseed() {
        let s = thread_rng().iter_map(|rng| uniform(rng)).take(256).collect::<Vec<usize>>();
        let mut r: StdRng = SeedableRng::from_seed(&s[..]);
        let string1 = r.gen_ascii_chars().take(100).collect::<String>();

        r.reseed(&s);

        let string2 = r.gen_ascii_chars().take(100).collect::<String>();
        assert_eq!(string1, string2);
    }
}
