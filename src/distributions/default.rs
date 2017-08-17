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

use Rng;
use distributions::{Distribution, Rand};
use distributions::uniform::{Uniform, Uniform01, codepoint};

/// A generic random value distribution. Generates values using what appears to
/// be "the best" distribution for each type, but ultimately the choice is arbitrary.
/// 
/// Makes use of the following distributions:
/// 
/// *   [`Uniform`] for integer types
/// *   [`Uniform01`] for floating point types
/// 
/// Makes use of the following methods:
/// 
/// *   [`codepoint`] for `char`
/// 
/// TODO: link
#[derive(Debug)]
pub struct Default;

// ----- implementations -----

impl<T: Rand<Uniform>> Distribution<T> for Default {
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> T {
        T::rand(rng, Uniform)
    }
}

// FIXME: https://github.com/rust-lang/rust/issues/23341
// impl<T: Rand<Uniform01>> Distribution<T> for Default {
//     fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> T {
//         T::rand(rng, Uniform01)
//     }
// }
// workaround above issue:
impl Distribution<f32> for Default {
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> f32 {
        f32::rand(rng, Uniform01)
    }
}
impl Distribution<f64> for Default {
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> f64 {
        f64::rand(rng, Uniform01)
    }
}

impl Distribution<char> for Default {
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> char {
        codepoint(rng)
    }
}


#[cfg(test)]
mod tests {
    use {Rng, thread_rng};
    use distributions::{Rand, Default};
    
    #[test]
    fn test_types() {
        let rng: &mut Rng = &mut thread_rng();
        fn do_test<T: Rand<Default>>(rng: &mut Rng) -> T {
            T::rand(rng, Default)
        }
        
        do_test::<u32>(rng);
        do_test::<i8>(rng);
        do_test::<f32>(rng);
        do_test::<f64>(rng);
        #[cfg(feature = "i128_support")]
        do_test::<u128>(rng);
        do_test::<char>(rng);
        do_test::<bool>(rng);
    }
}
