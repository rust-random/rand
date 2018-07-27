// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! This crate provides three things:
//! 
//! -   a portable implementation of `SipHasher`
//! -   `SipRng`, based around the `SipHash` state and mixing operations
//! -   `Seeder`, a universal seeder

#![doc(html_logo_url = "https://www.rust-lang.org/logos/rust-logo-128x128-blk.png",
       html_favicon_url = "https://www.rust-lang.org/favicon.ico",
       html_root_url = "https://docs.rs/rand_seeder/0.1.0")]

#![deny(missing_docs)]
#![deny(missing_debug_implementations)]
#![doc(test(attr(allow(unused_variables), deny(warnings))))]

#![no_std]

extern crate rand_core;

mod sip;

pub use sip::{SipHasher, SipRng};

use core::hash::Hash;
use rand_core::{RngCore, SeedableRng};

/// A universal seeder.
/// 
/// `Seeder` can be used to seed any `SeedableRng` from any hashable value. It
/// is portable and reproducible, and should turn any input into a good RNG
/// seed. It is intended for use in simulations and games where reproducibility
/// is important.
/// 
/// We do not recommend using `Seeder` for cryptographic applications and
/// strongly advise against usage for authentication (password hashing).
/// 
/// Example:
/// 
/// ```rust
/// # extern crate rand_core;
/// # extern crate rand_seeder;
/// use rand_core::RngCore;
/// use rand_seeder::{Seeder, SipRng};
/// 
/// // Use any SeedableRng you like in place of SipRng:
/// let mut rng: SipRng = Seeder::from("stripy zebra").make_rng();
/// println!("First value: {}", rng.next_u32());
/// ```
#[derive(Debug, Clone)]
pub struct Seeder {
    rng: SipRng,
}

impl Seeder {
    /// Construct an RNG (of type `R: SeedableRng`), seeded from the internal
    /// `SipRng`.
    /// 
    /// Mutliple RNGs may be constructed using the same `Seeder`.
    pub fn make_rng<R: SeedableRng>(&mut self) -> R {
        let mut seed = R::Seed::default();
        self.rng.fill_bytes(seed.as_mut());
        R::from_seed(seed)
    }
}

impl<H: Hash> From<H> for Seeder {
    #[inline]
    fn from(h: H) -> Seeder {
        let hasher = SipHasher::from(h);
        Seeder {
            rng: hasher.make_rng()
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    
    #[test]
    fn make_seeder() {
        let _ = Seeder::from(0u64);
        let _ = Seeder::from("a static string");
        let _ = Seeder::from([1u8, 2, 3]);
    }
    
    #[test]
    fn make_rng() {
        let mut seeder = Seeder::from("test string");
        let mut rng = seeder.make_rng::<SipRng>();
        assert_eq!(rng.next_u64(), 7267854722795183454);
        assert_eq!(rng.next_u64(), 602994585684902144);
    }
}
