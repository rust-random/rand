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
//! in generic code, use the `distributions` module. This includes
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
//! use rand::random;
//!
//! if random() { // random bool
//!     let a: i32 = random();
//!     let b: u32 = random();
//!     println!("i32: {}, u32: {}", a, b)
//! }
//! ```
//!
//! ```rust
//! use rand::thread_rng;
//! use rand::distributions::{Rand, Uniform, Uniform01};
//! let mut rng = thread_rng();
//! let tuple = (f64::rand(&mut rng, Uniform01), u8::rand(&mut rng, Uniform));
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
//! use rand::distributions::{Rand, Range};
//!
//! fn main() {
//!    let between = Range::new(-1f64, 1.);
//!    let mut rng = rand::thread_rng();
//!
//!    let total = 1_000_000;
//!    let mut in_circle = 0;
//!
//!    for _ in 0..total {
//!        let a = f64::rand(&mut rng, between);
//!        let b = f64::rand(&mut rng, between);
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
//! use rand::distributions::{Distribution, Range, uniform};
//! use rand::distributions::range::RangeInt;
//! use rand::sequences::Choose;
//!
//! struct SimulationResult {
//!     win: bool,
//!     switch: bool,
//! }
//!
//! // Run a single simulation of the Monty Hall problem.
//! fn simulate<R: Rng>(random_door: &Range<RangeInt<u32>>, rng: &mut R)
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
//!     *choices[..].choose(rng).unwrap()
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
//!     let random_door = Range::new(0u32, 3);
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

#![cfg_attr(not(feature="std"), no_std)]
#![cfg_attr(feature = "i128_support", feature(i128_type, i128))]

// We need to use several items from "core" for no_std support.
#[cfg(feature="std")]
extern crate core;

extern crate rand_core;

pub use rand_core::{Rng, SeedFromRng, SeedableRng, Error, Result};

#[cfg(feature="std")]
pub use read::ReadRng;
#[cfg(feature="std")]
pub use os::OsRng;
pub use iter::iter;
pub use distributions::{Distribution, Default, Rand};
#[cfg(feature="std")]
pub use thread_local::{ThreadRng, thread_rng, random, random_with};

use prng::IsaacWordRng;
use distributions::range::Range;

pub mod distributions;
pub mod iter;
pub mod prng;
pub mod reseeding;
pub mod sequences;
pub mod utils;

#[cfg(feature="std")]
mod os;
#[cfg(feature="std")]
mod read;
#[cfg(feature="std")]
mod thread_local;

/// Support mechanism for creating securely seeded objects 
/// using the OS generator.
/// Intended for use by RNGs, but not restricted to these.
/// 
/// This is implemented automatically for any PRNG implementing `SeedFromRng`,
/// and for normal types shouldn't be implemented directly. For mock generators
/// it may be useful to implement this instead of `SeedFromRng`.
#[cfg(feature="std")]
pub trait NewSeeded: Sized {
    /// Creates a new instance, automatically seeded via `OsRng`.
    fn new() -> Result<Self>;
}

#[cfg(feature="std")]
impl<R: SeedFromRng> NewSeeded for R {
    fn new() -> Result<Self> {
        let mut r = OsRng::new()?;
        Self::from_rng(&mut r)
    }
}

use distributions::range::SampleRange;

/// Extension trait on [`Rng`] with some convenience methods.
/// 
/// This trait exists to allow syntax like `rng.gen()` and
/// `rng.gen_range(1, 7)`. None of the methods in this trait are any more than
/// wrappers around functionality which exists elsewhere in the trait.
pub trait Sample: Rng {
    /// Sample a new value, using the given distribution.
    /// 
    /// ### Example
    /// 
    /// ```rust
    /// use rand::{thread_rng, Sample};
    /// use rand::distributions::Uniform;
    /// 
    /// let mut rng = thread_rng();
    /// let x: i32 = rng.sample(Uniform);
    /// ```
    fn sample<T, D: Distribution<T>>(&mut self, distr: D) -> T;
    
    /// Sample a new value, using the [`Default`] distribution.
    /// 
    /// ### Example
    /// 
    /// ```rust
    /// use rand::{thread_rng, Sample};
    /// 
    /// let mut rng = thread_rng();
    /// let x: i32 = rng.gen();
    /// ```
    fn gen<T>(&mut self) -> T where Default: Distribution<T> {
        self.sample(Default)
    }
    
    /// Sample a new value, using the [`Range`] distribution.
    /// 
    /// ### Example
    /// 
    /// ```rust
    /// use rand::{thread_rng, Sample};
    /// 
    /// let mut rng = thread_rng();
    /// 
    /// // simulate dice roll
    /// let x = rng.gen_range(1, 7);
    /// ```
    /// 
    /// If the same range is used repeatedly, some work can be saved by
    /// constructing the `Range` once and using it with `sample`:
    /// 
    /// ```rust
    /// use rand::{thread_rng, Sample};
    /// use rand::distributions::Range;
    /// 
    /// let mut rng = thread_rng();
    /// let die_range = Range::new(1, 7);
    /// 
    /// for _ in 0..100 {
    ///     let x = rng.sample(die_range);
    ///     assert!(1 <= x && x <= 6);
    /// }
    /// ```
    fn gen_range<T: SampleRange>(&mut self, low: T, high: T) -> T {
        assert!(low < high, "Sample::gen_range called with low >= high");
        Range::new(low, high).sample(self)
    }
    
    /// Construct an iterator on an `Rng`.
    /// 
    /// ### Example
    /// 
    /// ```rust
    /// use rand::{thread_rng, Sample};
    /// use rand::distributions::AsciiWordChar;
    /// 
    /// let mut rng = thread_rng();
    /// let x: String = rng.iter().map(|rng| rng.sample(AsciiWordChar)).take(6).collect();
    /// ```
    fn iter<'a>(&'a mut self) -> iter::Iter<'a, Self> {
        iter(self)
    }
}

impl<R: Rng+?Sized> Sample for R {
    fn sample<T, D: Distribution<T>>(&mut self, distr: D) -> T {
        distr.sample(self)
    }
}

/// The standard RNG. This is designed to be efficient on the current
/// platform.
/// 
/// The underlying algorithm is not fixed, thus values from this generator
/// cannot be guaranteed to be reproducible. For this reason, `StdRng` does
/// not support `SeedableRng`.
#[derive(Copy, Clone, Debug)]
pub struct StdRng {
    rng: IsaacWordRng,
}

impl Rng for StdRng {
    fn next_u32(&mut self) -> u32 {
        self.rng.next_u32()
    }
    fn next_u64(&mut self) -> u64 {
        self.rng.next_u64()
    }
    #[cfg(feature = "i128_support")]
    fn next_u128(&mut self) -> u128 {
        self.rng.next_u128()
    }
    fn try_fill(&mut self, dest: &mut [u8]) -> Result<()> {
        self.rng.try_fill(dest)
    }
}

impl SeedFromRng for StdRng {
    fn from_rng<R: Rng+?Sized>(other: &mut R) -> Result<Self> {
        IsaacWordRng::from_rng(other).map(|rng| StdRng{ rng })
    }
}


#[cfg(test)]
mod test {
    use {Rng, thread_rng, Sample, Result};
    use rand_core::mock::MockAddRng;
    use distributions::{uniform};
    use distributions::{Uniform, Range, Exp};
    use sequences::Shuffle;
    use std::iter::repeat;

    #[derive(Debug)]
    pub struct MyRng<R: ?Sized> { inner: R }

    impl<R: Rng+?Sized> Rng for MyRng<R> {
        fn next_u32(&mut self) -> u32 {
            self.inner.next_u32()
        }
        fn next_u64(&mut self) -> u64 {
            self.inner.next_u64()
        }
        #[cfg(feature = "i128_support")]
        fn next_u128(&mut self) -> u128 {
            self.inner.next_u128()
        }
        fn try_fill(&mut self, dest: &mut [u8]) -> Result<()> {
            self.inner.try_fill(dest)
        }
    }

    pub fn rng() -> MyRng<::ThreadRng> {
        MyRng { inner: ::thread_rng() }
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
        let mut r = MockAddRng::new(0x11_22_33_44_55_66_77_88u64, 0);

        // check every remainder mod 8, both in small and big vectors.
        let lengths = [0, 1, 2, 3, 4, 5, 6, 7,
                       80, 81, 82, 83, 84, 85, 86, 87];
        for &n in lengths.iter() {
            let mut v = repeat(0u8).take(n).collect::<Vec<_>>();
            r.try_fill(&mut v).unwrap();

            // use this to get nicer error messages.
            for (i, &byte) in v.iter().enumerate() {
                if byte == 0 {
                    panic!("byte {} of {} is zero", i, n)
                }
            }
        }
    }

    #[test]
    fn test_thread_rng() {
        let mut r = thread_rng();
        uniform::<i32, _>(&mut r);
        let mut v = [1, 1, 1];
        v.shuffle(&mut r);
        let b: &[_] = &[1, 1, 1];
        assert_eq!(v, b);
        assert_eq!(r.gen_range(0, 1), 0);
    }

    #[test]
    fn test_rng_trait_object() {
        let mut rng = thread_rng();
        {
            let r = &mut rng as &mut Rng;
            r.next_u32();
            uniform::<i32, _>(r);
            let mut v = [1, 1, 1];
            v[..].shuffle(r);
            let b: &[_] = &[1, 1, 1];
            assert_eq!(v, b);
            assert_eq!(r.gen_range(0, 1), 0);
        }
        {
            let mut r = Box::new(rng) as Box<Rng>;
            r.next_u32();
            uniform::<i32, _>(&mut r);
            let mut v = [1, 1, 1];
            v[..].shuffle(&mut *r);
            let b: &[_] = &[1, 1, 1];
            assert_eq!(v, b);
            assert_eq!(r.gen_range(0, 1), 0);
        }
    }

    #[test]
    fn test_sample_from_rng() {
        // use a static Rng type:
        let mut rng = thread_rng();
        
        let _a: u32 = rng.sample(Uniform);
        let _b = rng.sample(Range::new(-2, 15));
        
        // use a dynamic Rng type:
        let rng: &mut Rng = &mut thread_rng();
        
        let _c = rng.sample(Exp::new(2.0));
    }
}
