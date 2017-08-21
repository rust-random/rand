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
use std::sync::Mutex;

use {Rng, OsRng, Rand, Default};

// use reseeding::{Reseeder, ReseedingRng};
// 
// /// Controls how the thread-local RNG is reseeded.
// #[derive(Debug)]
// struct ThreadRngReseeder;
// 
// impl Reseeder<StdRng> for ThreadRngReseeder {
//     fn reseed(&mut self, rng: &mut StdRng) {
//         *rng = match StdRng::new() {
//             Ok(r) => r,
//             Err(e) => panic!("could not reseed thread_rng: {}", e)
//         }
//     }
// }
// 
// const THREAD_RNG_RESEED_THRESHOLD: u64 = 32_768;
// type ReseedingStdRng = ReseedingRng<StdRng, ThreadRngReseeder>;
//     thread_local!(static THREAD_RNG_KEY: Rc<RefCell<Option<Box<Rng>>>> = {
//         let r = match StdRng::new() {
//             Ok(r) => r,
//             Err(e) => panic!("could not initialize thread_rng: {}", e)
//         };
//         let rng = ReseedingRng::new(r,
//                                                THREAD_RNG_RESEED_THRESHOLD,
//                                                ThreadRngReseeder);

/// The thread-local RNG.
#[derive(Clone)]
#[allow(missing_debug_implementations)]
pub struct ThreadRng {
    rng: Rc<RefCell<Box<Rng>>>,
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

thread_local!(
    static THREAD_RNG_CREATOR: Mutex<RefCell<Box<Fn() -> Box<Rng>>>> = {
        // TODO: should this panic?
        Mutex::new(RefCell::new(Box::new(|| Box::new(OsRng::new().unwrap()))))
    }
);

thread_local!(
    static THREAD_RNG_KEY: Rc<RefCell<Box<Rng>>> = {
        let rng = THREAD_RNG_CREATOR.with(|f| {
            let creator = f.lock().unwrap();
            let rng = (creator.borrow())();
            rng
        });
        Rc::new(RefCell::new(rng))
    }
);

/// Retrieve the lazily-initialized thread-local random number
/// generator, seeded by the system. This is used by `random` and
/// `random_with` to generate new values, and may be used directly with other
/// distributions: `Range::new(0, 10).sample(&mut thread_rng())`.
///
/// By default, this uses `OsRng` which pulls random numbers directly from the
/// operating system. This is intended to be a good secure default; for more
/// see `set_thread_rng` and `set_new_thread_rng`.
/// 
/// This is intended to provide securely generated random numbers, but this
/// behaviour can be changed by `set_thread_rng` and `set_new_thread_rng`.
/// 
/// `thread_rng` is not especially fast, since it uses dynamic dispatch and
/// `OsRng`, which requires a system call on each usage. Users wanting a fast
/// generator for games or simulations may prefer not to use `thread_rng` at
/// all, especially if reproducibility of results is important.
pub fn thread_rng() -> ThreadRng {
    ThreadRng { rng: THREAD_RNG_KEY.with(|t| t.clone()) }
}

/// Set the thread-local RNG used by `thread_rng`. Only affects the current
/// thread. See also `set_new_thread_rng`.
/// 
/// If this is never called in a thread and `set_new_thread_rng` is never called
/// globally, the first call to `thread_rng()` in the thread will create a new
/// `OsRng` and use that as a source of numbers.
/// This method allows a different generator to be set, and can be called at
/// any time to set a new generator.
/// 
/// Calling this affects all users of `thread_rng`, `random` and `random_with`
/// in the current thread, including libraries. Users should ensure the
/// generator used is secure enough for all users of `thread_rng`, including
/// other libraries.
/// 
/// This may have some use in testing, by spawning a new thread, overriding the
/// generator with known values (a constant or a PRNG with known seed), then
/// asserting the exact output of "randomly" generated values. The use of a new
/// thread avoids affecting other users of `thread_rng`.
/// 
/// ```rust
/// use rand::{ConstRng, random, set_thread_rng};
/// use std::thread;
/// 
/// thread::spawn(move || {
///     set_thread_rng(Box::new(ConstRng::new(123u32)));
///     assert_eq!(random::<u32>(), 123u32);
/// });
/// ```
pub fn set_thread_rng(rng: Box<Rng>) {
    THREAD_RNG_KEY.with(|t| *t.borrow_mut() = rng);
}

/// Control how thread-local generators are created for new threads.
/// 
/// The first time `thread_rng()` is called in each thread, this closure is
/// used to create a new generator. If this closure has not been set, the
/// built-in closure returning a new boxed `OsRng` is used.
/// 
/// Calling this affects all users of `thread_rng`, `random` and `random_with`
/// in all new threads (as well as existing threads which haven't called
/// `thread_rng` yet), including libraries. Users should ensure the generator
/// used is secure enough for all users of `thread_rng`, including other
/// libraries.
/// 
/// This closure should not panic; doing so would kill whichever thread is
/// calling `thread_rng` at the time, poison its mutex, and cause all future
/// threads initialising a `thread_rng` (or calling this function) to panic.
pub fn set_new_thread_rng(creator: Box<Fn() -> Box<Rng>>) {
    THREAD_RNG_CREATOR.with(|f| {
        let p = f.lock().unwrap();
        *p.borrow_mut() = creator;
    });
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

#[cfg(test)]
mod test {
    use std::thread;
    use {set_thread_rng, random, ConstRng};
    
    #[test]
    fn test_set_thread_rng() {
        let v = 12u64;
        thread::spawn(move || {
            random::<u64>();
            // affect this thread only:
            set_thread_rng(Box::new(ConstRng::new(v)));
            assert_eq!(random::<u64>(), v);
            assert_eq!(random::<u64>(), v);
        });
        
        // The chance of 128 bits randomly equalling our value is miniscule:
        let (x, y): (u64, u64) = (random(), random());
        assert!((x, y) != (v, v));
    }
}
