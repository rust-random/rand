// Copyright 2017-2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Thread-local random number generator

use std::cell::RefCell;
use std::rc::Rc;

use {RngCore, StdRng, SeedableRng, EntropyRng};
use {Distribution, Uniform, Rng, Error};
use reseeding::ReseedingRng;


/// The type returned by [`thread_rng`], essentially just a reference to the
/// PRNG in thread-local memory.
/// 
/// [`thread_rng`]: fn.thread_rng.html
#[derive(Clone, Debug)]
pub struct ThreadRng {
    rng: Rc<RefCell<ReseedingRng<StdRng, EntropyRng>>>,
}

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
pub fn thread_rng() -> ThreadRng {
    ThreadRng { rng: THREAD_RNG_KEY.with(|t| t.clone()) }
}

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
#[inline]
pub fn random<T>() -> T where Uniform: Distribution<T> {
    thread_rng().gen()
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    #[cfg(feature="std")]
    #[cfg(not(all(target_arch = "wasm32", not(target_os = "emscripten"))))]
    fn test_thread_rng() {
        let mut r = ::thread_rng();
        r.gen::<i32>();
        let mut v = [1, 1, 1];
        r.shuffle(&mut v);
        let b: &[_] = &[1, 1, 1];
        assert_eq!(v, b);
        assert_eq!(r.gen_range(0, 1), 0);
    }

    #[test]
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
