// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The ChaCha random number generator.

#![doc(html_logo_url = "https://www.rust-lang.org/logos/rust-logo-128x128-blk.png",
       html_favicon_url = "https://www.rust-lang.org/favicon.ico",
       html_root_url = "https://rust-random.github.io/rand/")]

#![deny(missing_docs)]
#![deny(missing_debug_implementations)]
#![doc(test(attr(allow(unused_variables), deny(warnings))))]

#![cfg_attr(not(feature = "std"), no_std)]

extern crate c2_chacha;
pub extern crate generic_array;
pub extern crate rand_core;

mod chacha;

use generic_array::typenum;

pub use chacha::{ChaChaXRng, ChaChaXCore};
/// ChaCha with 20 rounds
pub type ChaCha20Rng = ChaChaXRng<typenum::U10>;
/// ChaCha with 12 rounds
pub type ChaCha12Rng = ChaChaXRng<typenum::U6>;
/// ChaCha with 8 rounds
pub type ChaCha8Rng = ChaChaXRng<typenum::U4>;
/// ChaCha with 20 rounds
pub type ChaChaRng = ChaCha20Rng;
/// ChaCha with 20 rounds, low-level interface
pub type ChaChaCore = ChaChaXCore<typenum::U10>;
