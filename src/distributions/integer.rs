// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The implementations of the `Standard` distribution for integer types.

use {Rng};
use distributions::{Distribution, Standard};

impl Distribution<u8> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u8 {
        rng.next_u32() as u8
    }
}

impl Distribution<u16> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u16 {
        rng.next_u32() as u16
    }
}

impl Distribution<u32> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u32 {
        rng.next_u32()
    }
}

impl Distribution<u64> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u64 {
        rng.next_u64()
    }
}

#[cfg(feature = "i128_support")]
impl Distribution<u128> for Standard {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> u128 {
        // Use LE; we explicitly generate one value before the next.
        let x = rng.next_u64() as u128;
        let y = rng.next_u64() as u128;
        (y << 64) | x
    }
}

impl Distribution<usize> for Standard {
    #[inline]
    #[cfg(any(target_pointer_width = "32", target_pointer_width = "16"))]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> usize {
        rng.next_u32() as usize
    }

    #[inline]
    #[cfg(target_pointer_width = "64")]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> usize {
        rng.next_u64() as usize
    }
}

macro_rules! impl_int_from_uint {
    ($ty:ty, $uty:ty) => {
        impl Distribution<$ty> for Standard {
            #[inline]
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                rng.gen::<$uty>() as $ty
            }
        }
    }
}

impl_int_from_uint! { i8, u8 }
impl_int_from_uint! { i16, u16 }
impl_int_from_uint! { i32, u32 }
impl_int_from_uint! { i64, u64 }
#[cfg(feature = "i128_support")] impl_int_from_uint! { i128, u128 }
impl_int_from_uint! { isize, usize }


#[cfg(test)]
mod tests {
    use Rng;
    use distributions::{Standard};
    
    #[test]
    fn test_integers() {
        let mut rng = ::test::rng(806);
        
        rng.sample::<isize, _>(Standard);
        rng.sample::<i8, _>(Standard);
        rng.sample::<i16, _>(Standard);
        rng.sample::<i32, _>(Standard);
        rng.sample::<i64, _>(Standard);
        #[cfg(feature = "i128_support")]
        rng.sample::<i128, _>(Standard);
        
        rng.sample::<usize, _>(Standard);
        rng.sample::<u8, _>(Standard);
        rng.sample::<u16, _>(Standard);
        rng.sample::<u32, _>(Standard);
        rng.sample::<u64, _>(Standard);
        #[cfg(feature = "i128_support")]
        rng.sample::<u128, _>(Standard);
    }
}
