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
use distributions::Distribution;
use distributions::uniform::{Uniform, Uniform01, Codepoint};

/// A generic random value distribution. Generates values using what appears to
/// be "the best" distribution for each type, but ultimately the choice is arbitrary.
/// 
/// Makes use of the following distributions:
/// 
/// *   [`Uniform`] for integer types
/// *   [`Uniform01`] for floating point types
/// *   [`Codepoint`] for `char`
/// 
/// TODO: link
#[derive(Debug)]
pub struct Default;

// ----- implementations -----

impl<T> Distribution<T> for Default where Uniform: Distribution<T>{
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> T {
        Uniform.sample(rng)
    }
}

// FIXME: https://github.com/rust-lang/rust/issues/23341
// impl<T> Distribution<T> for Default where Uniform01: Distribution<T>{
//     fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> T {
//         Uniform01.sample(rng)
//     }
// }
// workaround above issue:
impl Distribution<f32> for Default {
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> f32 {
        Uniform01.sample(rng)
    }
}
impl Distribution<f64> for Default {
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> f64 {
        Uniform01.sample(rng)
    }
}

impl Distribution<char> for Default {
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> char {
        Codepoint.sample(rng)
    }
}


#[cfg(test)]
mod tests {
    use {Rng, Sample, thread_rng};
    use distributions::{Default};
    
    #[test]
    fn test_types() {
        let rng: &mut Rng = &mut thread_rng();
        
        rng.sample::<u32, _>(Default);
        rng.sample::<i8, _>(Default);
        rng.sample::<f32, _>(Default);
        rng.sample::<f64, _>(Default);
        #[cfg(feature = "i128_support")]
        rng.sample::<u128, _>(Default);
        rng.sample::<char, _>(Default);
        rng.sample::<bool, _>(Default);
    }
}
