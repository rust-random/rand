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
//!
//! Note on determinism:
//! It's slightly tricky to build a parallel simulation using Rayon
//! which is both efficient *and* reproducible.
//!
//! Rayon's ParallelIterator api does not guarantee that the work will be
//! batched into identical batches on every run, so we can't simply use
//! map_init to construct one RNG per Rayon batch.
//!
//! Instead, we do our own batching, so that a Rayon work item becomes a
//! batch. Then we can fix our rng stream to the batched work item.
//! Batching amortizes the cost of constructing the Rng from a fixed seed
//! over BATCH_SIZE trials. Manually batching also turns out to be faster
//! for the nondeterministic version of this program as well.

use rand::distr::{Distribution, Uniform};
use rand_chacha::{rand_core::SeedableRng, ChaCha8Rng};
use rayon::prelude::*;

static SEED: u64 = 0;
static BATCH_SIZE: u64 = 10_000;
static BATCHES: u64 = 1000;

fn main() {
    let range = Uniform::new(-1.0f64, 1.0).unwrap();

    let in_circle = (0..BATCHES)
        .into_par_iter()
        .map(|i| {
            let mut rng = ChaCha8Rng::seed_from_u64(SEED);
            // We chose ChaCha because it's fast, has suitable statistical properties for simulation,
            // and because it supports this set_stream() api, which lets us choose a different stream
            // per work item. ChaCha supports 2^64 independent streams.
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
        .sum::<usize>();

    // assert this is deterministic
    assert_eq!(in_circle, 7852263);

    // prints something close to 3.14159...
    println!(
        "π is approximately {}",
        4. * (in_circle as f64) / ((BATCH_SIZE * BATCHES) as f64)
    );
}
