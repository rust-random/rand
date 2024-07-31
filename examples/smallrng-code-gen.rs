extern crate rand;
use std::hint::black_box;

use rand::prelude::*;
use rand::rngs::SmallRng;

#[inline(never)]
pub fn small_from_thread_rng() -> SmallRng {
    SmallRng::from_thread_rng()
}

#[inline(never)]
pub fn small_from_small_rng(rng: &mut SmallRng) -> SmallRng {
    SmallRng::from_rng(rng)
}

#[inline(never)]
pub fn small_from_seed(seed: [u8; 32]) -> SmallRng {
    SmallRng::from_seed(seed)
}

#[inline(never)]
pub fn small_seed_from_u64(seed: u64) -> SmallRng {
    SmallRng::seed_from_u64(seed)
}

#[inline(never)]
pub fn small_next_u64(rng: &mut SmallRng) -> u64 {
    rng.next_u64()
}

/// This example is meant for usage with cargo asm to check code generation
/// for the performance sensitive SmallRng.
/// Example: `cargo asm -p rand --example smallrng-code-gen`
fn main() {
    let mut a = small_from_thread_rng();
    let b = small_from_small_rng(black_box(&mut a));
    dbg!(b);
    let b = small_from_seed(black_box([0; 32]));
    dbg!(b);
    let b = small_seed_from_u64(black_box(0));
    dbg!(b);
    let b = small_next_u64(black_box(&mut a));
    dbg!(b);
}
