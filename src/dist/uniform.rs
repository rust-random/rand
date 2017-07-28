// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Generating uniformly distributed numbers
//! 
//! TODO: is there value in having both `uniform` and `Uniform`?

use std::mem;
use std::marker::PhantomData;

use Rng;
use dist::Sample;

/// Sample values uniformly over the whole range supported by the type
pub fn uniform<T: SampleUniform, R: Rng>(rng: &mut R) -> T {
    T::sample_uniform(rng)
}

/// Sample values uniformly over the whole range supported by the type
pub trait SampleUniform: Sized {
    /// Sample a value from a RNG
    fn sample_uniform<R: Rng>(rng: &mut R) -> Self;
}

impl SampleUniform for isize {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> isize {
        if mem::size_of::<isize>() == 4 {
            rng.gen::<i32>() as isize
        } else {
            rng.gen::<i64>() as isize
        }
    }
}

impl SampleUniform for i8 {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> i8 {
        rng.next_u32() as i8
    }
}

impl SampleUniform for i16 {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> i16 {
        rng.next_u32() as i16
    }
}

impl SampleUniform for i32 {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> i32 {
        rng.next_u32() as i32
    }
}

impl SampleUniform for i64 {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> i64 {
        rng.next_u64() as i64
    }
}

#[cfg(feature = "i128_support")]
impl SampleUniform for i128 {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> i128 {
        rng.gen::<u128>() as i128
    }
}

impl SampleUniform for usize {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> usize {
        if mem::size_of::<usize>() == 4 {
            rng.gen::<u32>() as usize
        } else {
            rng.gen::<u64>() as usize
        }
    }
}

impl SampleUniform for u8 {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> u8 {
        rng.next_u32() as u8
    }
}

impl SampleUniform for u16 {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> u16 {
        rng.next_u32() as u16
    }
}

impl SampleUniform for u32 {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> u32 {
        rng.next_u32()
    }
}

impl SampleUniform for u64 {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> u64 {
        rng.next_u64()
    }
}

#[cfg(feature = "i128_support")]
impl SampleUniform for u128 {
    #[inline]
    fn sample_uniform<R: Rng>(rng: &mut R) -> u128 {
        ((rng.next_u64() as u128) << 64) | (rng.next_u64() as u128)
    }
}

/// Sample values uniformly over the whole range supported by the type.
/// 
/// No internal state.
#[derive(Clone, Copy, Debug, Default)]
pub struct Uniform<T: SampleUniform> {
    _marker: PhantomData<T>,
}

impl<T: SampleUniform> Uniform<T> {
    /// Create an instance. Should optimise to nothing, since there is no
    /// internal state.
    pub fn new() -> Self {
        Uniform {
            _marker: PhantomData
        }
    }
}

impl<T: SampleUniform> Sample<T> for Uniform<T> {
    fn sample<R: Rng>(&self, rng: &mut R) -> T {
        T::sample_uniform(rng)
    }
}


#[cfg(test)]
mod tests {
    use dist::{uniform, Uniform, Sample};
    use dist::uniform::SampleUniform;
    
    #[test]
    fn test_integers() {
        let mut rng = ::test::rng();
        
        let _: i32 = SampleUniform::sample_uniform(&mut rng);
        let _: i32 = i32::sample_uniform(&mut rng);
        
        let _: isize = uniform(&mut rng);
        let _: i8 = uniform(&mut rng);
        let _: i16 = uniform(&mut rng);
        let _: i32 = uniform(&mut rng);
        let _: i64 = uniform(&mut rng);
        #[cfg(feature = "i128_support")]
        let _: i128 = uniform(&mut rng);
        
        let _: usize = uniform(&mut rng);
        let _: u8 = uniform(&mut rng);
        let _: u16 = uniform(&mut rng);
        let _: u32 = uniform(&mut rng);
        let _: u64 = uniform(&mut rng);
        #[cfg(feature = "i128_support")]
        let _: u128 = uniform(&mut rng);
        
        let dist = Uniform::<u8>::new();
        let _ = dist.sample(&mut rng);
    }
}
