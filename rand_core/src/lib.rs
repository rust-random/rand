// Copyright 2017-2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Random number generation traits
//! 
//! This version of `rand_core` is a compatibility shim around version 0.3.
//! 
//! This crate is mainly of interest to crates publishing implementations of
//! [`RngCore`]. Other users are encouraged to use the [rand] crate instead
//! which re-exports the main traits and error types.
//!
//! [`RngCore`] is the core trait implemented by algorithmic pseudo-random number
//! generators and external random-number sources.
//! 
//! [`SeedableRng`] is an extension trait for construction from fixed seeds and
//! other random number generators.
//! 
//! [`Error`] is provided for error-handling. It is safe to use in `no_std`
//! environments.
//! 
//! The [`impls`] and [`le`] sub-modules include a few small functions to assist
//! implementation of [`RngCore`].
//! 
//! [rand]: https://crates.io/crates/rand
//! [`RngCore`]: trait.RngCore.html
//! [`SeedableRng`]: trait.SeedableRng.html
//! [`Error`]: struct.Error.html
//! [`impls`]: impls/index.html
//! [`le`]: le/index.html

#![doc(html_logo_url = "https://www.rust-lang.org/logos/rust-logo-128x128-blk.png",
       html_favicon_url = "https://www.rust-lang.org/favicon.ico",
       html_root_url = "https://docs.rs/rand_core/0.2.2")]

#![deny(missing_docs)]
#![deny(missing_debug_implementations)]
#![doc(test(attr(allow(unused_variables), deny(warnings))))]

#![no_std]

extern crate rand_core as core3;

pub use core3::{ErrorKind, Error};
pub use core3::{block, impls, le};
pub use core3::{RngCore, CryptoRng, SeedableRng};
