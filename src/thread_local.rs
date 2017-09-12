// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Thread-local handle to a random number generator

use std::cell::RefCell;
use std::rc::Rc;

use {Rng, StdRng, NewSeeded, Rand, Default, Result};

use reseeding::{ReseedingRng, ReseedWithNew};

const THREAD_RNG_RESEED_THRESHOLD: u64 = 32_768;
type ReseedingStdRng = ReseedingRng<StdRng, ReseedWithNew>;

/// The thread-local RNG.
#[derive(Clone)]
#[allow(missing_debug_implementations)]
pub struct ThreadRng {
    rng: Rc<RefCell<ReseedingStdRng>>,
}

impl Rng for ThreadRng {
    fn next_u32(&mut self) -> u32 {
        self.rng.borrow_mut().next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        self.rng.borrow_mut().next_u64()
    }
    
    #[cfg(feature = "i128_support")]
    fn next_u128(&mut self) -> u128 {
        self.rng.borrow_mut().next_u128()
    }
    
    fn try_fill(&mut self, bytes: &mut [u8]) -> Result<()> {
        self.rng.borrow_mut().try_fill(bytes)
    }
}

thread_local!(
    static THREAD_RNG_KEY: Rc<RefCell<ReseedingStdRng>> = {
        let r = match StdRng::new() {
            Ok(r) => r,
            Err(e) => panic!("could not initialize thread_rng: {:?}", e)
        };
        let rng = ReseedingRng::new(r,
                                               THREAD_RNG_RESEED_THRESHOLD,
                                               ReseedWithNew);
        Rc::new(RefCell::new(rng))
    }
);

/// Retrieve the lazily-initialized thread-local random number
/// generator, seeded by the system. This is used by `random` and
/// `random_with` to generate new values, and may be used directly with other
/// distributions: `Range::new(0, 10).sample(&mut thread_rng())`.
///
/// Uses `StdRng` internally, set to reseed from `OsRng` periodically.
/// This should provide a reasonable compromise between speed and security;
/// while the generator is not approved for crytographic usage its output should
/// be hard to guess, and performance should be similar to non-cryptographic
/// generators.
pub fn thread_rng() -> ThreadRng {
    ThreadRng { rng: THREAD_RNG_KEY.with(|t| t.clone()) }
}

/// Generates a random value using the thread-local random number generator.
///
/// `random()` can generate various types of random things, and so may require
/// type hinting to generate the specific type you want. It uses
/// `distributions::SampleDefault` to determine *how* values are generated for each type.
///
/// This function uses the thread local random number generator. This means
/// that if you're calling `random()` in a loop, caching the generator can
/// increase performance. An example is shown below.
///
/// # Examples
///
/// ```
/// let x = rand::random::<u8>();
/// println!("{}", x);
///
/// if rand::random() { // generates a boolean
///     println!("Better lucky than good!");
/// }
/// ```
///
/// Caching the thread local random number generator:
///
/// ```
/// use rand::{Rand, Default};
///
/// let mut v = vec![1, 2, 3];
///
/// for x in v.iter_mut() {
///     *x = rand::random()
/// }
///
/// // would be faster as
///
/// let mut rng = rand::thread_rng();
///
/// for x in v.iter_mut() {
///     *x = Rand::rand(&mut rng, Default);
/// }
/// ```
/// 
/// Note that the above example uses `SampleDefault` which is a zero-sized
/// marker type.
#[inline]
pub fn random<T: Rand<Default>>() -> T {
    T::rand(&mut thread_rng(), Default)
}

/// Generates a random value using the thread-local random number generator.
/// 
/// This is a more flexible variant of `random()`, supporting selection of the
/// distribution used. For example:
/// 
/// ```
/// use rand::random_with;
/// use rand::distributions::{Rand, Default, Uniform01, Closed01, Range};
/// 
/// // identical to calling `random()`:
/// let x: f64 = random_with(Default);
/// 
/// // same distribution, since Default uses Uniform01 for floats:
/// let y: f64 = random_with(Uniform01);
/// 
/// // use the closed range [0, 1] inseat of half-open [0, 1):
/// let z: f64 = random_with(Closed01);
/// 
/// // use the half-open range [0, 2):
/// let w: f64 = random_with(Range::new(0.0, 2.0));
/// 
/// // Note that constructing a `Range` is non-trivial, so for the last example
/// // it might be better to do this if sampling a lot:
/// let mut rng = rand::thread_rng();
/// let range = Range::new(0.0, 2.0);
/// // Do this bit many times:
/// let v = f64::rand(&mut rng, range);
/// ```
#[inline]
pub fn random_with<D, T: Rand<D>>(distribution: D) -> T {
    T::rand(&mut thread_rng(), distribution)
}
