// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Generic value creation

use std::fmt;
use std::marker::PhantomData;

use Rng;
use dist::Distribution;
use dist::uniform::{SampleUniform, /*SampleUniform01,*/ codepoint};

/// A generic random value creator. Generates values using what appears to be
/// an appropriate distribution for each type, but choice is arbitrary.
/// 
/// Makes use of the following traits on the types implementing them:
/// 
/// *   [`SampleUniform`] for integer types
/// *   [`SampleUniform01`] for floating point types (FIXME)
/// 
/// Makes use of the following methods:
/// 
/// *   [`codepoint`] for `char`
/// 
/// TODO: link
/// 
/// TODO: is this useful? Personally I feel not, but it carries over previous
/// functionality.
#[derive(Default)]
pub struct DefaultDist<T: SampleDefault> {
    _marker: PhantomData<T>,
}

impl<T: SampleDefault> DefaultDist<T> {
    /// Create an instance. Should optimise to nothing, since there is no
    /// internal state.
    pub fn new() -> Self {
        DefaultDist {
            _marker: PhantomData
        }
    }
}

impl<T: SampleDefault> Copy for DefaultDist<T> {}

// derive only auto-impls for types T: Clone, but we don't have that restriction
impl<T: SampleDefault> Clone for DefaultDist<T> {
    fn clone(&self) -> Self {
        DefaultDist::new()
    }
}

// derive only auto-impls for types T: Debug, but we don't have that restriction
impl<T: SampleDefault> fmt::Debug for DefaultDist<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "DefaultDist {{}}")
    }
}

impl<T: SampleDefault> Distribution<T> for DefaultDist<T> {
    fn sample<R: Rng>(&self, rng: &mut R) -> T {
        T::sample_default(rng)
    }
}


// ----- SampleDefault -----

/// Types supporting default sampling (see `DefaultDist`)
pub trait SampleDefault {
    /// Sample a value using an RNG
    fn sample_default<R: Rng>(rng: &mut R) -> Self;
}

impl<T: SampleUniform> SampleDefault for T {
    fn sample_default<R: Rng>(rng: &mut R) -> Self {
        T::sample_uniform(rng)
    }
}
// FIXME: https://github.com/rust-lang/rust/issues/23341
// impl<T: SampleUniform01> SampleDefault for T {
//     fn sample_default<R: Rng>(rng: &mut R) -> T {
//         T::sample_uniform01(rng)
//     }
// }
impl SampleDefault for char {
    fn sample_default<R: Rng>(rng: &mut R) -> char {
        codepoint(rng)
    }
}


#[cfg(test)]
mod tests {
    use {Rng, thread_rng};
    use dist::Distribution;
    use dist::default::{DefaultDist, SampleDefault};
    
    
    #[test]
    fn test_types() {
        let mut rng = thread_rng();
        fn do_test<T: SampleDefault, R: Rng>(rng: &mut R) -> T {
            let dist = DefaultDist::<T>::new();
            dist.sample(rng)
        }
        
        do_test::<u32, _>(&mut rng);
        do_test::<i8, _>(&mut rng);
        // FIXME (see above)
        // do_test::<f32, _>(&mut rng);
        // do_test::<f64, _>(&mut rng);
        #[cfg(feature = "i128_support")]
        do_test::<u128, _>(&mut rng);
        do_test::<char, _>(&mut rng);
        do_test::<bool, _>(&mut rng);
    }
}
