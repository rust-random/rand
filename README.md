# Rand

[![Build Status](https://travis-ci.org/rust-lang-nursery/rand.svg?branch=master)](https://travis-ci.org/rust-lang-nursery/rand)
[![Build Status](https://ci.appveyor.com/api/projects/status/github/rust-lang-nursery/rand?svg=true)](https://ci.appveyor.com/project/alexcrichton/rand)
[![crates.io](https://img.shields.io/crates/v/rand.svg)](https://crates.io/crates/rand)
[![docs.rs](https://docs.rs/rand/badge.svg)](https://docs.rs/rand)

A Rust library for random number generators and other randomness functionality.

See also:

*   [rand_core](https://crates.io/crates/rand_core)

Documentation:
[master branch](https://rust-lang-nursery.github.io/rand/rand/index.html),
[by release](https://docs.rs/rand)

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
rand = "0.5.0-pre.0"
```

and this to your crate root:

```rust
extern crate rand;

// example usage:
use rand::{Rng, thread_rng};
let x: f64 = thread_rng().gen();
```

## Versions

Version 0.5 is in development and contains many breaking changes; expected
release date is approx. end of March 2018 if all goes well.

Version 0.4 was released in December 2017. It contains almost no breaking
changes since the 0.3 series.

For more details, see the [changelog](CHANGELOG.md).

### Rust version requirements

The 0.5 release of Rand will require **Rustc version 1.22 or greater**.
Rand 0.4 and 0.3 (since approx. June 2017) require Rustc version 1.15 or
greater. Subsets of the Rand code may work with older Rust versions, but this
is not supported.

Travis CI always has a build with a pinned version of Rustc matching the oldest
supported Rust release. The current policy is that this can be updated in any
Rand release if required, but the change must be noted in the changelog.

## Functionality

The `rand_core` crate provides:

-   base random number generator traits
-   error-reporting types
-   functionality to aid implementation of RNGs

The `rand` crate provides:

-   most content from `rand_core` (re-exported)
-   fresh entropy: `EntropyRng`, `OsRng`, `JitterRng`
-   pseudo-random number generators: `StdRng`, `SmallRng`, `prng` module
-   convenient, auto-seeded crypto-grade thread-local generator: `thread_rng`
-   `distributions` producing many different types of random values:
    -   `Uniform`-ly distributed integers and floats of many types
    -   unbiased sampling from specified `Range`s
    -   sampling from exponential/normal/gamma distributions
    -   sampling from binomial/poisson distributions
    -   `gen_bool` aka Bernoulli distribution
-   `seq`-uence related functionality:
    -   sampling a subset of elements
    -   randomly shuffling a list

## Crate Features

By default, Rand is built with all stable features available. The following
optional features are available:

-   `alloc` can be used instead of `std` to provide `Vec` and `Box`
-   `i128_support` enables support for generating `u128` and `i128` values
-   `log` enables some logging via the `log` crate
-   `nightly` enables all unstable features (`i128_support`)
-   `serde-1` enables serialisation for some types, via Serde version 1
-   `wasm-stdweb` enables support for `OsRng` on WASM via stdweb.
-   `std` enabled by default; by setting "default-features = false" `no_std`
    mode is activated; this removes features depending on `std` functionality:
    -   `OsRng` is entirely unavailable
    -   `JitterRng` code is still present, but a nanosecond timer must be
        provided via `JitterRng::new_with_timer`
    -   Since no external entropy is available, it is not possible to create
        generators with fresh seeds (user must provide entropy)
    -   `thread_rng`, `weak_rng` and `random` are all disabled
    -   exponential, normal and gamma type distributions are unavailable
        since `exp` and `log` functions are not provided in `core`
    -   any code requiring `Vec` or `Box`

## Testing

Unfortunately, `cargo test` does not test everything. The following tests are
recommended:

```
# Basic tests for Rand and sub-crates
cargo test --all

# Test no_std support
cargo test --tests --no-default-features
# Test no_std+alloc support
cargo test --tests --no-default-features --features alloc

# Test log and serde support
cargo test --features serde-1,log

# Test 128-bit support (requires nightly)
cargo test --all --features nightly

# Benchmarks (requires nightly)
cargo bench
# or just to test the benchmark code:
cargo test --benches
```


# License

Rand is distributed under the terms of both the MIT
license and the Apache License (Version 2.0).

See [LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT) for details.
