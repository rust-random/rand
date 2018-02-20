// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The implementations of the `Uniform` distribution for integer types.

use core::mem;

use {Rng};
use distributions::{Distribution, Uniform};

impl Distribution<isize> for Uniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> isize {
        if mem::size_of::<isize>() == 4 {
            rng.gen::<i32>() as isize
        } else {
            rng.gen::<i64>() as isize
        }
    }
}

impl Distribution<i8> for Uniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> i8 {
        rng.next_u32() as i8
    }
}

impl Distribution<i16> for Uniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> i16 {
        rng.next_u32() as i16
    }
}

impl Distribution<i32> for Uniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> i32 {
        rng.next_u32() as i32
    }
}

impl Distribution<i64> for Uniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> i64 {
        rng.next_u64() as i64
    }
}

#[cfg(feature = "i128_support")]
impl Distribution<i128> for Uniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> i128 {
        rng.gen::<u128>() as i128
    }
}

impl Distribution<usize> for Uniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> usize {
        if mem::size_of::<usize>() == 4 {
            rng.gen::<u32>() as usize
        } else {
            rng.gen::<u64>() as usize
        }
    }
}

impl Distribution<u8> for Uniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u8 {
        rng.next_u32() as u8
    }
}

impl Distribution<u16> for Uniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u16 {
        rng.next_u32() as u16
    }
}

impl Distribution<u32> for Uniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u32 {
        rng.next_u32()
    }
}

impl Distribution<u64> for Uniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u64 {
        rng.next_u64()
    }
}

#[cfg(feature = "i128_support")]
impl Distribution<u128> for Uniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u128 {
        ((rng.next_u64() as u128) << 64) | (rng.next_u64() as u128)
    }
}
