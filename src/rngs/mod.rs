// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Convenience RNGs

pub mod adaptor;

#[cfg(feature="std")] mod entropy;
#[doc(hidden)] pub mod jitter;
pub mod mock;   // Public so we don't export `StepRng` directly, making it a bit
                // more clear it is intended for testing.
#[cfg(feature="std")] #[doc(hidden)] pub mod os;
mod small;
mod std;
#[cfg(feature="std")] pub(crate) mod thread;


pub use self::jitter::{JitterRng, TimerError};
#[cfg(feature="std")] pub use self::entropy::EntropyRng;
#[cfg(feature="std")] pub use self::os::OsRng;

pub use self::small::SmallRng;
pub use self::std::StdRng;
#[cfg(feature="std")] pub use self::thread::ThreadRng;
