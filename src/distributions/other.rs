// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The implementations of the `Uniform` distribution for other built-in types.

use core::char;

use {Rng};
use distributions::{Distribution, Uniform, Range};

// ----- Sampling distributions -----

/// Sample a `char`, uniformly distributed over ASCII letters and numbers:
/// a-z, A-Z and 0-9.
/// 
/// # Example
///
/// ```rust
/// use std::iter;
/// use rand::{Rng, thread_rng};
/// use rand::distributions::Alphanumeric;
/// 
/// let mut rng = thread_rng();
/// let chars: String = iter::repeat(())
///         .map(|()| rng.sample(Alphanumeric))
///         .take(7)
///         .collect();
/// println!("Random chars: {}", chars);
/// ```
#[derive(Debug)]
pub struct Alphanumeric;


// ----- Implementations of distributions -----

impl Distribution<char> for Uniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> char {
        let range = Range::new(0u32, 0x11_0000);
        loop {
            match char::from_u32(range.sample(rng)) {
                Some(c) => return c,
                // About 0.2% of numbers in the range 0..0x110000 are invalid
                // codepoints (surrogates).
                None => {}
            }
        }
    }
}

impl Distribution<char> for Alphanumeric {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> char {
        const RANGE: u32 = 26 + 26 + 10;
        const GEN_ASCII_STR_CHARSET: &'static [u8] =
            b"ABCDEFGHIJKLMNOPQRSTUVWXYZ\
                abcdefghijklmnopqrstuvwxyz\
                0123456789";
        loop {
            let var = rng.next_u32() >> 26;
            if var < RANGE {
                return GEN_ASCII_STR_CHARSET[var as usize] as char
            }
        }
    }
}

impl Distribution<bool> for Uniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> bool {
        // We can compare against an arbitrary bit of an u32 to get a bool.
        // Because the least significant bits of a lower quality RNG can have
        // simple patterns, we compare against the most significant bit. This is
        // easiest done using a sign test.
        (rng.next_u32() as i32) < 0
    }
}

macro_rules! tuple_impl {
    // use variables to indicate the arity of the tuple
    ($($tyvar:ident),* ) => {
        // the trailing commas are for the 1 tuple
        impl< $( $tyvar ),* >
            Distribution<( $( $tyvar ),* , )>
            for Uniform
            where $( Uniform: Distribution<$tyvar> ),*
        {
            #[inline]
            fn sample<R: Rng + ?Sized>(&self, _rng: &mut R) -> ( $( $tyvar ),* , ) {
                (
                    // use the $tyvar's to get the appropriate number of
                    // repeats (they're not actually needed)
                    $(
                        _rng.gen::<$tyvar>()
                    ),*
                    ,
                )
            }
        }
    }
}

impl Distribution<()> for Uniform {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, _: &mut R) -> () { () }
}
tuple_impl!{A}
tuple_impl!{A, B}
tuple_impl!{A, B, C}
tuple_impl!{A, B, C, D}
tuple_impl!{A, B, C, D, E}
tuple_impl!{A, B, C, D, E, F}
tuple_impl!{A, B, C, D, E, F, G}
tuple_impl!{A, B, C, D, E, F, G, H}
tuple_impl!{A, B, C, D, E, F, G, H, I}
tuple_impl!{A, B, C, D, E, F, G, H, I, J}
tuple_impl!{A, B, C, D, E, F, G, H, I, J, K}
tuple_impl!{A, B, C, D, E, F, G, H, I, J, K, L}

macro_rules! array_impl {
    // recursive, given at least one type parameter:
    {$n:expr, $t:ident, $($ts:ident,)*} => {
        array_impl!{($n - 1), $($ts,)*}

        impl<T> Distribution<[T; $n]> for Uniform where Uniform: Distribution<T> {
            #[inline]
            fn sample<R: Rng + ?Sized>(&self, _rng: &mut R) -> [T; $n] {
                [_rng.gen::<$t>(), $(_rng.gen::<$ts>()),*]
            }
        }
    };
    // empty case:
    {$n:expr,} => {
        impl<T> Distribution<[T; $n]> for Uniform {
            fn sample<R: Rng + ?Sized>(&self, _rng: &mut R) -> [T; $n] { [] }
        }
    };
}

array_impl!{32, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T, T,}

impl<T> Distribution<Option<T>> for Uniform where Uniform: Distribution<T> {
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Option<T> {
        // UFCS is needed here: https://github.com/rust-lang/rust/issues/24066
        if rng.gen::<bool>() {
            Some(rng.gen())
        } else {
            None
        }
    }
}


#[cfg(test)]
mod tests {
    use {Rng, RngCore, Uniform};
    #[cfg(all(not(feature="std"), feature="alloc"))] use alloc::String;
    
    #[test]
    fn test_misc() {
        let mut rng: &mut RngCore = &mut ::test::rng(820);
        
        rng.sample::<char, _>(Uniform);
        rng.sample::<bool, _>(Uniform);
    }
    
    #[cfg(any(feature="std", feature="alloc"))]
    #[test]
    fn test_chars() {
        use core::iter;
        use distributions::Alphanumeric;
        let mut rng = ::test::rng(805);
        
        let c = rng.sample(Alphanumeric);
        assert!((c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z'));
        
        let word: String = iter::repeat(())
                .map(|()| rng.sample(Alphanumeric)).take(5).collect();
        assert_eq!(word.len(), 5);
    }
}
