extern crate rand;
extern crate wasm_bindgen;
extern crate wasm_bindgen_test;

use rand::rngs::StdRng;
use rand::Rng;
use rand::SeedableRng;
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn generate_from_seed(seed: u32) -> u32 {
    StdRng::seed_from_u64(seed as u64).gen()
}

pub mod tests {
    use wasm_bindgen_test::*;

    #[wasm_bindgen_test]
    fn generate_from_seed() {
        let _ = super::generate_from_seed(42);
    }
}
