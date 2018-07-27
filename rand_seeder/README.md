# rand_seeder

[![Build Status](https://travis-ci.org/rust-lang-nursery/rand.svg)](https://travis-ci.org/rust-lang-nursery/rand)
[![Build Status](https://ci.appveyor.com/api/projects/status/github/rust-lang-nursery/rand?svg=true)](https://ci.appveyor.com/project/dhardy/rand)
[![Latest version](https://img.shields.io/crates/v/rand_seeder.svg)](https://crates.io/crates/rand_seeder)
[![Documentation](https://docs.rs/rand_seeder/badge.svg)](https://docs.rs/rand_seeder)
[![Minimum rustc version](https://img.shields.io/badge/rustc-1.22+-yellow.svg)](https://github.com/rust-lang-nursery/rand#rust-version-requirements)
[![License](https://img.shields.io/crates/l/rand_seeder.svg)](https://github.com/rust-lang-nursery/rand/tree/master/rand_seeder#license)

A universal seeder based on [`SipHash`](https://131002.net/siphash/).

This crate provides three things:

-   a portable implementation of SipHash-2-4, `SipHasher`
-   `SipRng`, based around the `SipHash` state and mixing operations
-   `Seeder`, a convenience wrapper

`Seeder` can be used to seed any `SeedableRng` from any hashable value. It is
portable and reproducible, and should turn any input into a good RNG seed.
It is intended for use in simulations and games where reproducibility is
important.

We do not recommend using `Seeder` for cryptographic applications and
strongly advise against usage for authentication (password hashing).

Example:

```rust
use rand_core::RngCore;         // for next_u32
use rand::prng::XorShiftRng;    // or whatever you like
use rand_seeder::Seeder;

let mut rng: XorShiftRng = Seeder::from("stripy zebra").make_rng();
println!("First value: {}", rng.next_u32());
```

Documentation:
[master branch](https://rust-lang-nursery.github.io/rand/rand_seeder/index.html),
[by release](https://docs.rs/rand_seeder)

[Changelog](CHANGELOG.md)

[rand]: https://crates.io/crates/rand


# License

`rand_seeder` is distributed under the terms of both the MIT license and the
Apache License (Version 2.0).

See [LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT) for details.
