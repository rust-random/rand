Rand
====

A Rust library for random number generators and other randomness functionality.

[![Build Status](https://travis-ci.org/rust-lang-nursery/rand.svg?branch=master)](https://travis-ci.org/rust-lang-nursery/rand)
[![Build status](https://ci.appveyor.com/api/projects/status/rm5c9o33k3jhchbw?svg=true)](https://ci.appveyor.com/project/alexcrichton/rand)

[Documentation](https://docs.rs/rand)

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
rand = "0.4"
```

and this to your crate root:

```rust
extern crate rand;
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

## Examples

There is built-in support for a random number generator (RNG) associated with each thread stored in thread-local storage. This RNG can be accessed via thread_rng, or used implicitly via random. This RNG is normally randomly seeded from an operating-system source of randomness, e.g. /dev/urandom on Unix systems, and will automatically reseed itself from this source after generating 32 KiB of random data.

```rust
let tuple = rand::random::<(f64, char)>();
println!("{:?}", tuple)
```

```rust
use rand::Rng;

let mut rng = rand::thread_rng();
if rng.gen() { // random bool
    println!("i32: {}, u32: {}", rng.gen::<i32>(), rng.gen::<u32>())
}
```

It is also possible to use other RNG types, which have a similar interface. The following uses the "ChaCha" algorithm instead of the default.

```rust
use rand::{Rng, ChaChaRng};

let mut rng = rand::ChaChaRng::new_unseeded();
println!("i32: {}, u32: {}", rng.gen::<i32>(), rng.gen::<u32>())
```

## Features

By default, Rand is built with all stable features available. The following
optional features are available:

-   `alloc` can be used instead of `std` to provide `Vec` and `Box`
-   `i128_support` enables support for generating `u128` and `i128` values
-   `log` enables some logging via the `log` crate
-   `nightly` enables all unstable features (`i128_support`)
-   `serde-1` enables serialisation for some types, via Serde version 1
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
