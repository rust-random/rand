extern crate rand;
extern crate wasm_bindgen;

use rand::rngs::{OsRng, StdRng};
use rand::FromEntropy;
use rand::{Rng, RngCore, SeedableRng};
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn generate_from_seed(seed: u32) -> i32 {
    StdRng::seed_from_u64(seed as u64).gen()
}

#[wasm_bindgen]
pub fn generate_from_os_rand() -> i32 {
    OsRng::new().unwrap().gen()
}

#[wasm_bindgen]
pub fn generate_from_entropy() -> i32 {
    StdRng::from_entropy().gen()
}
