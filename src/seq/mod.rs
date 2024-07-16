// Copyright 2018-2023 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Sequence-related functionality
//!
//! This module provides:
//!
//! *   [`IndexedRandom`] for sampling slices and other indexable lists
//! *   [`IndexedMutRandom`] for sampling slices and other mutably indexable lists
//! *   [`SliceRandom`] for mutating slices
//! *   [`IteratorRandom`] for sampling iterators
//! *   [`index::sample`] low-level API to choose multiple indices from
//!     `0..length`
//!
//! Also see:
//!
//! *   [`crate::distributions::WeightedIndex`] distribution which provides
//!     weighted index sampling.
//!
//! In order to make results reproducible across 32-64 bit architectures, all
//! `usize` indices are sampled as a `u32` where possible (also providing a
//! small performance boost in some cases).

mod coin_flipper;
mod increasing_uniform;
mod iterator;
mod slice;

pub mod index;

#[cfg(feature = "alloc")]
#[doc(no_inline)]
pub use crate::distributions::WeightError;
pub use iterator::IteratorRandom;
#[cfg(feature = "alloc")]
pub use slice::SliceChooseIter;
pub use slice::{IndexedMutRandom, IndexedRandom, SliceRandom};

use crate::Rng;

// Sample a number uniformly between 0 and `ubound`. Uses 32-bit sampling where
// possible, primarily in order to produce the same output on 32-bit and 64-bit
// platforms.
#[inline]
fn gen_index<R: Rng + ?Sized>(rng: &mut R, ubound: usize) -> usize {
    if ubound <= (u32::MAX as usize) {
        rng.gen_range(0..ubound as u32) as usize
    } else {
        rng.gen_range(0..ubound)
    }
}
