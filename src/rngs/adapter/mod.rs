// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Wrappers / adapters forming RNGs

#[cfg(feature="std")] #[doc(hidden)] pub mod read;
mod reseeding;

#[cfg(feature="std")] pub use self::read::ReadRng;
pub use self::reseeding::ReseedingRng;
