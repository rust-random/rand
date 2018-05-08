// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Various RNGs and wrappers.

#[cfg(feature="std")] mod entropy;
mod jitter;
pub mod mock;
#[cfg(feature="std")] mod os;
#[cfg(feature="std")] mod read;
mod reseeding;
mod small;
mod std;
#[cfg(feature="std")] mod thread;

// Sources of external randomness
#[cfg(feature="std")] pub use self::entropy::EntropyRng;
pub use self::jitter::{JitterRng, TimerError};
#[cfg(feature="std")] pub use self::os::OsRng;

// Wrappers
#[cfg(feature="std")] pub use self::read::ReadRng;
pub use self::reseeding::ReseedingRng;
#[doc(hidden)] pub use self::small::SmallRng;
#[doc(hidden)] pub use self::std::StdRng;
#[cfg(feature="std")] pub use self::thread::ThreadRng;
