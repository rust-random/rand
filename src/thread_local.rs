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

use {Rng, StdRng, Rand, Default};
use reseeding::{Reseeder, ReseedingRng};

/// Controls how the thread-local RNG is reseeded.
#[derive(Debug)]
struct ThreadRngReseeder;

impl Reseeder<StdRng> for ThreadRngReseeder {
    fn reseed(&mut self, rng: &mut StdRng) {
        *rng = match StdRng::new() {
            Ok(r) => r,
            Err(e) => panic!("could not reseed thread_rng: {}", e)
        }
    }
}

const THREAD_RNG_RESEED_THRESHOLD: u64 = 32_768;
type ThreadRngInner = ReseedingRng<StdRng, ThreadRngReseeder>;

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
        let rng = ReseedingRng::new(r,
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
