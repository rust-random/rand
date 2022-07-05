// Copyright 2018 Developers of the Rand project.
// Copyright 2013-2018 The Rust Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! # Monte Carlo estimation of π with a chosen seed and rayon for parallelism
//!
//! Imagine that we have a square with sides of length 2 and a unit circle
//! (radius = 1), both centered at the origin. The areas are:
//!
//! ```text
//!     area of circle  = πr² = π * r * r = π
//!     area of square  = 2² = 4
//! ```
//!
//! The circle is entirely within the square, so if we sample many points
//! randomly from the square, roughly π / 4 of them should be inside the circle.
//!
//! We can use the above fact to estimate the value of π: pick many points in
//! the square at random, calculate the fraction that fall within the circle,
//! and multiply this fraction by 4.

#![cfg(all(feature = "std", feature = "std_rng"))]

use rand::distributions::{Distribution, Uniform};
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha8Rng;
use rayon::prelude::*;

static SEED: u64 = 0;

fn main() {
    let range = Uniform::new(-1.0f64, 1.0);

    let total = 1_000_000;
    let cha_cha = ChaCha8Rng::seed_from_u64(SEED);

    let in_circle: usize = (0..total)
        .into_par_iter()
        .map_init(
            || cha_cha.clone(),
            |rng, i| {
                // ChaCha supports indexing into its stream. We need this because due to work-stealing, 
                // Rayon does not guarantee that the same work items will be run in the same order
                // between runs of the program. We can only guarantee determinism by setting the stream 
                // according to the work number.
                rng.set_word_pos(i);
                let a = range.sample(rng);
                let b = range.sample(rng);
                if a * a + b * b <= 1.0 {
                    1
                } else {
                    0
                }
            },
        )
        .reduce(|| 0, |a, b| a + b);
    // prints something close to 3.14159...
    println!(
        "π is approximately {}",
        4. * (in_circle as f64) / (total as f64)
    );
}
