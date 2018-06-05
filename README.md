# Rand

[![Build Status](https://travis-ci.org/rust-lang-nursery/rand.svg?branch=master)](https://travis-ci.org/rust-lang-nursery/rand)
[![Build Status](https://ci.appveyor.com/api/projects/status/github/rust-lang-nursery/rand?svg=true)](https://ci.appveyor.com/project/alexcrichton/rand)
[![Latest version](https://img.shields.io/crates/v/rand.svg)](https://crates.io/crates/rand)
[![Documentation](https://docs.rs/rand/badge.svg)](https://docs.rs/rand)
[![Minimum rustc version](https://img.shields.io/badge/rustc-1.22+-yellow.svg)](https://github.com/rust-lang-nursery/rand#rust-version-requirements)

A Rust library for random number generation.

Rand provides utilities to generate random numbers, to convert them to useful
types and distributions, and some randomness-related algorithms.

The core random number generation traits of Rand live in the [rand_core](
https://crates.io/crates/rand_core) crate; this crate is most useful when
implementing RNGs.

API reference:
[master branch](https://rust-lang-nursery.github.io/rand/rand/index.html),
[by release](https://docs.rs/rand/0.5).

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
rand = "0.5"
```

and this to your crate root:

```rust
extern crate rand;

use rand::prelude::*;

fn main() {
  // basic usage with random():
  let x: u8 = random();
  println!("{}", x);

  let y = random::<f64>();
  println!("{}", y);

  if random() { // generates a boolean
      println!("Heads!");
  }

  // normal usage needs both an RNG and a function to generate the appropriate
  // type, range, distribution, etc.
  let mut rng = thread_rng();
  if rng.gen() { // random bool
      let x: f64 = rng.gen(); // random number in range [0, 1)
      println!("x is: {}", x);
      let ch = rng.gen::<char>(); // Sometimes you need type annotation
      println!("char is: {}", ch);
      println!("Number from 0 to 9: {}", rng.gen_range(0, 10));
  }
}
```

## Functionality

The Rand crate provides:

- A convenient to use default RNG, `thread_rng`: an automatically seeded,
  crypto-grade generator stored in thread-local memory.
- Pseudo-random number generators: `StdRng`, `SmallRng`, `prng` module.
- Functionality for seeding PRNGs: the `FromEntropy` trait, and as sources of
  external randomness `EntropyRng`, `OsRng` and `JitterRng`.
- Most content from [`rand_core`](https://crates.io/crates/rand_core)
  (re-exported): base random number generator traits and error-reporting types.
- 'Distributions' producing many different types of random values:
  - A `Standard` distribution for integers, floats, and derived types including
    tuples, arrays and `Option`
  - Unbiased sampling from specified `Uniform` ranges.
  - Sampling from exponential/normal/gamma distributions.
  - Sampling from binomial/poisson distributions.
  - `gen_bool` aka Bernoulli distribution.
- `seq`-uence related functionality:
  - Sampling a subset of elements.
  - Randomly shuffling a list.


## Versions

Version 0.5 is the latest version and contains many breaking changes.
See [the Upgrade Guide](UPDATING.md) for guidance on updating from previous
versions.

Version 0.4 was released in December 2017. It contains almost no breaking
changes since the 0.3 series.

For more details, see the [changelog](CHANGELOG.md).

### Rust version requirements

The 0.5 release of Rand requires **Rustc version 1.22 or greater**.
Rand 0.4 and 0.3 (since approx. June 2017) require Rustc version 1.15 or
greater. Subsets of the Rand code may work with older Rust versions, but this
is not supported.

Travis CI always has a build with a pinned version of Rustc matching the oldest
supported Rust release. The current policy is that this can be updated in any
Rand release if required, but the change must be noted in the changelog.


## Crate Features

Rand is built with only the `std` feature enabled by default. The following
optional features are available:

- `alloc` can be used instead of `std` to provide `Vec` and `Box`.
- `i128_support` enables support for generating `u128` and `i128` values.
- `log` enables some logging via the `log` crate.
- `nightly` enables all unstable features (`i128_support`).
- `serde1` enables serialization for some types, via Serde version 1.
- `stdweb` enables support for `OsRng` on `wasm-unknown-unknown` via `stdweb`
  combined with `cargo-web`.

`no_std` mode is activated by setting `default-features = false`; this removes
functionality depending on `std`:

- `thread_rng()`, and `random()` are not available, as they require thread-local
  storage and an entropy source.
- `OsRng` and `EntropyRng` are unavailable.
- `JitterRng` code is still present, but a nanosecond timer must be provided via
  `JitterRng::new_with_timer`
- Since no external entropy is available, it is not possible to create
  generators with fresh seeds using the `FromEntropy` trait (user must provide
  a seed).
- Exponential, normal and gamma type distributions are unavailable since `exp`
  and `log` functions are not provided in `core`.
- The `seq`-uence module is unavailable, as it requires `Vec`.


# License

Rand is distributed under the terms of both the MIT license and the
Apache License (Version 2.0).

See [LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT) for details.
