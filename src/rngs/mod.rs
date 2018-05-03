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

mod small;
mod std;
#[cfg(feature="std")] pub(crate) mod thread;

pub use self::small::SmallRng;
pub use self::std::StdRng;
#[cfg(feature="std")] pub use self::thread::ThreadRng;
