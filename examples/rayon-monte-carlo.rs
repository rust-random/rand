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
use rand_chacha::{rand_core::SeedableRng, ChaCha8Rng};
use rayon::prelude::*;

static SEED: u64 = 0;
static BATCH_SIZE: u64 = 10_000;
static BATCHES: u64 = 1000;

fn main() {
    let range = Uniform::new(-1.0f64, 1.0);

    // We have to manually batch the work so that we can get Rng construction
    // out of the hot loop. Due to work-stealing, ParallelIterator::map_init 
    // doesn't guarantee the same # and order of work items per run.
    let in_circle = (0..BATCHES)
        .into_par_iter()
        .map(|i| {
            let mut rng = ChaCha8Rng::seed_from_u64(SEED);
            // using set_stream() here force every batch to use a different part of the rng stream
            rng.set_stream(i);
            let mut count = 0;
            for _ in 0..BATCH_SIZE {
                let a = range.sample(&mut rng);
                let b = range.sample(&mut rng);
                if a * a + b * b <= 1.0 {
                    count += 1;
                }
            }
            count
        })
        .reduce(|| 0usize, |a, b| a + b);

        
    // prints something close to 3.14159...
    println!(
        "π is approximately {}",
        4. * (in_circle as f64) / ((BATCH_SIZE * BATCHES) as f64)
    );
}
