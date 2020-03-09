// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Weighted index sampling
//!
//! This module provides two implementations for sampling indices:
//!
//! *   [`WeightedIndex`] allows `O(log N)` sampling
//! *   [`alias_method::WeightedIndex`] allows `O(1)` sampling, but with
//!      much greater set-up cost
//!      
//! [`alias_method::WeightedIndex`]: alias_method/struct.WeightedIndex.html

pub mod alias_method;

pub use rand::distributions::weighted::{WeightedError, WeightedIndex};
