// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The ISAAC random number generator.

/// Select 32- or 64-bit variant dependent on pointer size.
#[cfg(target_pointer_width = "32")]
pub use prng::isaac::IsaacRng as IsaacWordRng;
#[cfg(target_pointer_width = "64")]
pub use prng::isaac64::Isaac64Rng as IsaacWordRng;
