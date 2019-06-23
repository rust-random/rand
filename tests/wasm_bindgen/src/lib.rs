// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Crate to test WASM with the `wasm-bindgen` lib.

#![doc(html_logo_url = "https://www.rust-lang.org/logos/rust-logo-128x128-blk.png")]

use rand::rngs::{OsRng, StdRng};
use rand::{Rng, SeedableRng};
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn generate_from_seed(seed: u32) -> i32 {
    StdRng::seed_from_u64(seed as u64).gen()
}

#[wasm_bindgen]
pub fn generate_from_os_rand() -> i32 {
    OsRng.gen()
}

#[wasm_bindgen]
pub fn generate_from_entropy() -> i32 {
    StdRng::from_entropy().gen()
}

pub mod tests {
    use wasm_bindgen_test::*;

    #[wasm_bindgen_test]
    fn generate_from_seed() {
        let _ = super::generate_from_seed(42);
    }

    #[wasm_bindgen_test]
    fn generate_from_os_rand() {
        let _ = super::generate_from_os_rand();
    }

    #[wasm_bindgen_test]
    fn generate_from_entropy() {
        let _ = super::generate_from_entropy();
    }
}
