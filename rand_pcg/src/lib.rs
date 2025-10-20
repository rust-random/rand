// Copyright 2018-2023 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! The PCG random number generators.
//!
//! This is a native Rust implementation of a small selection of [PCG generators].
//! The primary goal of this crate is simple, minimal, well-tested code; in
//! other words it is explicitly not a goal to re-implement all of PCG.
//!
//! ## Generators
//!
//! This crate provides:
//!
//! -   [`Pcg32`] aka [`Lcg64Xsh32`], officially known as `pcg32`, a general
//!     purpose RNG. This is a good choice on both 32-bit and 64-bit CPUs
//!     (for 32-bit output).
//! -   [`Pcg64`] aka [`Lcg128Xsl64`], officially known as `pcg64`, a general
//!     purpose RNG. This is a good choice on 64-bit CPUs.
//! -   [`Pcg64Mcg`] aka [`Mcg128Xsl64`], officially known as `pcg64_fast`,
//!     a general purpose RNG using 128-bit multiplications. This has poor
//!     performance on 32-bit CPUs but is a good choice on 64-bit CPUs for
//!     both 32-bit and 64-bit output.
//!
//! These generators are all deterministic and portable (see [Reproducibility]
//! in the book), with testing against reference vectors.
//!
//! ## Seeding (construction)
//!
//! Generators implement the [`SeedableRng`] trait. All methods are suitable for
//! seeding. Some suggestions:
//!
//! 1.  To automatically seed with a unique seed, use [`SeedableRng::from_rng`]
//!     with a master generator (here [`rand::rng()`](https://docs.rs/rand/latest/rand/fn.rng.html)):
//!     ```ignore
//!     use rand_core::SeedableRng;
//!     use rand_pcg::Pcg64Mcg;
//!     let rng = Pcg64Mcg::from_rng(&mut rand::rng());
//!     # let _: Pcg64Mcg = rng;
//!     ```
//! 2.  Seed **from an integer** via `seed_from_u64`. This uses a hash function
//!     internally to yield a (typically) good seed from any input.
//!     ```
//!     # use {rand_core::SeedableRng, rand_pcg::Pcg64Mcg};
//!     let rng = Pcg64Mcg::seed_from_u64(1);
//!     # let _: Pcg64Mcg = rng;
//!     ```
//!
//! See also [Seeding RNGs] in the book.
//!
//! ## Generation
//!
//! Generators implement [`RngCore`], whose methods may be used directly to
//! generate unbounded integer or byte values.
//! ```
//! use rand_core::{SeedableRng, RngCore};
//! use rand_pcg::Pcg64Mcg;
//!
//! let mut rng = Pcg64Mcg::seed_from_u64(0);
//! let x = rng.next_u64();
//! assert_eq!(x, 0x5603f242407deca2);
//! ```
//!
//! It is often more convenient to use the [`rand::Rng`] trait, which provides
//! further functionality. See also the [Random Values] chapter in the book.
//!
//! [PCG generators]: https://www.pcg-random.org/
//! [Reproducibility]: https://rust-random.github.io/book/crate-reprod.html
//! [Seeding RNGs]: https://rust-random.github.io/book/guide-seeding.html
//! [Random Values]: https://rust-random.github.io/book/guide-values.html
//! [`RngCore`]: rand_core::RngCore
//! [`SeedableRng`]: rand_core::SeedableRng
//! [`SeedableRng::from_rng`]: rand_core::SeedableRng#method.from_rng
//! [`rand::rng`]: https://docs.rs/rand/latest/rand/fn.rng.html
//! [`rand::Rng`]: https://docs.rs/rand/latest/rand/trait.Rng.html

#![doc(
    html_logo_url = "https://www.rust-lang.org/logos/rust-logo-128x128-blk.png",
    html_favicon_url = "https://www.rust-lang.org/favicon.ico",
    html_root_url = "https://rust-random.github.io/rand/"
)]
#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![deny(missing_debug_implementations)]
#![no_std]

mod pcg128;
mod pcg128cm;
mod pcg64;

pub use rand_core;

pub use self::pcg64::{Lcg64Xsh32, Pcg32};
pub use self::pcg128::{Lcg128Xsl64, Mcg128Xsl64, Pcg64, Pcg64Mcg};
pub use self::pcg128cm::{Lcg128CmDxsm64, Pcg64Dxsm};
