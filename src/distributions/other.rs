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
use distributions::{Distribution, Uniform};

impl Distribution<char> for Uniform {
    #[inline]
    fn sample<R: Rng>(&self, rng: &mut R) -> char {
        // a char is 21 bits
        const CHAR_MASK: u32 = 0x001f_ffff;
        loop {
            // Rejection sampling. About 0.2% of numbers with at most
            // 21-bits are invalid codepoints (surrogates), so this
            // will succeed first go almost every time.
            match char::from_u32(rng.next_u32() & CHAR_MASK) {
                Some(c) => return c,
                None => {}
            }
        }
    }
}

impl Distribution<bool> for Uniform {
    #[inline]
    fn sample<R: Rng>(&self, rng: &mut R) -> bool {
        rng.gen::<u8>() & 1 == 1
    }
}
