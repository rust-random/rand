// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! This crate implements the [xoshiro] family of pseudorandom number generators
//! designed by David Blackman and Sebastiano Vigna. They feature high
//! perfomance and a small state and superseed the previous xorshift-based
//! generators. However, they are no cryptographically secure and their output
//! can be predicted by observing a few samples.
//!
//! The following generators are implemented:
//!
//! # 64-bit generators
//! - [`Xoshiro256StarStar`]: Recommended for all purposes. Excellent speed and
//!   a state space (256 bits) large enough for any parallel application.
//! - [`Xoshiro256Plus`]: Recommended for generating 64-bit floating-point
//!   numbers. About 15% faster than `Xoshiro256StarStar`, but has a [low linear
//!   complexity] in the lowest bits (which are discarded when generating
//!   floats), making it fail linearity tests. This is unlikely to have any
//!   impact in practise.
//! - [`Xoroshiro128StarStar`]: An alternative to `Xoshiro256StarStar`, having
//!   the same speed but using half the state. Only suited for low-scale parallel
//!   applications.
//! - [`Xoroshiro128Plus`]: An alternative to `Xoshiro256Plus`, having the same
//!   speed but using half the state. Only suited for low-scale parallel
//!   applications. Has a [low linear complexity] in the lowest bits (which are
//!   discarded when generating floats), making it fail linearity tests. This is
//!   unlikely to have any impact in practise.
//! - [`Xoshiro512StarStar`]: An alternative to `Xoshiro256StarStar` with more
//!   state and the same speed.
//! - [`Xoshiro512Plus`]: An alternative to `Xoshiro512Plus` with more
//!   state and the same speed. Has a [low linear complexity] in the lowest bits
//!   (which are discarded when generating floats), making it fail linearity
//!   tests. This is unlikely to have any impact in practise.
//! - [`SplitMix64`]: Recommended for initializing generators of the xoshiro
//!   familiy from a 64-bit seed. Used for implementing `seed_from_u64`.
//!
//! # 32-bit generators
//! - [`Xoshiro128StarStar`]: Recommended for all purposes. Excellent speed.
//! - [`Xoshiro128Plus`]: Recommended for generating 32-bit floating-point
//!   numbers. Faster than `Xoshiro128StarStar`, but has a [low linear
//!   complexity] in the lowest bits (which are discarded when generating
//!   floats), making it fail linearity tests. This is unlikely to have any
//!   impact in practise.
//! - [`Xoroshiro64StarStar`]: An alternative to `Xoshiro128StarStar`, having
//!   the same speed but using half the state.
//! - [`Xoroshiro64Star`]: An alternative to `Xoshiro128Plus`, having the
//!   same speed but using half the state. Has a [low linear complexity] in the
//!   lowest bits (which are discarded when generating floats), making it fail
//!   linearity tests. This is unlikely to have any impact in practise.
//!
//! [xoshiro]: http://xoshiro.di.unimi.it/
//! [low linear complexity]: http://xoshiro.di.unimi.it/lowcomp.php
//! [`Xoshiro256StarStar`]: ./struct.Xoshiro256StarStar.html
//! [`Xoshiro256Plus`]: ./struct.Xoshiro256Plus.html
//! [`Xoroshiro128StarStar`]: ./struct.Xoroshiro128StarStar.html
//! [`Xoroshiro128Plus`]: ./struct.Xoroshiro128Plus.html
//! [`Xoshiro512StarStar`]: ./struct.Xoshiro512StarStar.html
//! [`Xoshiro512Plus`]: ./struct.Xoshiro512Plus.html
//! [`SplitMix64`]: ./struct.SplitMix64.html
//! [`Xoshiro128StarStar`]: ./struct.Xoshiro128StarStar.html
//! [`Xoshiro128Plus`]: ./struct.Xoshiro128Plus.html
//! [`Xoroshiro64StarStar`]: ./struct.Xoroshiro64StarStar.html
//! [`Xoroshiro64Star`]: ./struct.Xoroshiro64Star.html

#![doc(html_logo_url = "https://www.rust-lang.org/logos/rust-logo-128x128-blk.png",
       html_favicon_url = "https://www.rust-lang.org/favicon.ico",
       html_root_url = "https://docs.rs/rand_xoshiro/0.1.0")]

#![deny(missing_docs)]
#![deny(missing_debug_implementations)]
#![cfg_attr(feature = "cargo-clippy", allow(unreadable_literal))]
#![no_std]
extern crate byteorder;
extern crate rand_core;

#[macro_use]
mod common;
mod splitmix64;
mod xoshiro128starstar;
mod xoshiro128plus;
mod xoshiro256starstar;
mod xoshiro256plus;
mod xoshiro512starstar;
mod xoshiro512plus;
mod xoroshiro128plus;
mod xoroshiro128starstar;
mod xoroshiro64starstar;
mod xoroshiro64star;

pub use splitmix64::SplitMix64;
pub use xoshiro128starstar::Xoshiro128StarStar;
pub use xoshiro128plus::Xoshiro128Plus;
pub use xoshiro256starstar::Xoshiro256StarStar;
pub use xoshiro256plus::Xoshiro256Plus;
pub use common::Seed512;
pub use xoshiro512starstar::Xoshiro512StarStar;
pub use xoshiro512plus::Xoshiro512Plus;
pub use xoroshiro128plus::Xoroshiro128Plus;
pub use xoroshiro128starstar::Xoroshiro128StarStar;
pub use xoroshiro64starstar::Xoroshiro64StarStar;
pub use xoroshiro64star::Xoroshiro64Star;
