// Copyright 2025 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![allow(unused)]
#![cfg_attr(feature = "min_specialization", feature(min_specialization))]

use rand_core::{Fill, RngCore};

// Test that Fill may be implemented for externally-defined types
struct MyInt(i32);
impl<R: RngCore + ?Sized> Fill<R> for MyInt {
    fn fill_slice(this: &mut [Self], rng: &mut R) {
        todo!()
    }
}

// Test specialization on a local RNG
struct MyRng;
impl RngCore for MyRng {
    fn next_u32(&mut self) -> u32 {
        todo!()
    }
    fn next_u64(&mut self) -> u64 {
        todo!()
    }
    fn fill_bytes(&mut self, _: &mut [u8]) {
        todo!()
    }
}
#[cfg(feature = "min_specialization")]
impl Fill<MyRng> for u64 {
    fn fill_slice(this: &mut [Self], rng: &mut MyRng) {
        todo!()
    }
}
