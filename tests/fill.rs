// Copyright 2025 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![allow(unused)]

use rand::{Fill, Rng};

// Test that Fill may be implemented for externally-defined types
struct MyInt(i32);
impl Fill for MyInt {
    fn fill_slice<R: Rng + ?Sized>(this: &mut [Self], rng: &mut R) {
        todo!()
    }
}
