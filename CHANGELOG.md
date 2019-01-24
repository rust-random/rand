# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

A [separate changelog is kept for rand_core](rand_core/CHANGELOG.md).

You may also find the [Update Guide](UPDATING.md) useful.


## [0.5.6] - 2019-01-25
### Platforms
- Fuchsia: Replaced fuchsia-zircon with fuchsia-cprng


## [0.5.5] - 2018-08-07
### Documentation
- Fix links in documentation (#582)


## [0.5.4] - 2018-07-11
### Platform support
- Make `OsRng` work via WASM/stdweb for WebWorkers


## [0.5.3] - 2018-06-26
### Platform support
- OpenBSD, Bitrig: fix compilation (broken in 0.5.1) (#530)


## [0.5.2] - 2018-06-18
### Platform support
- Hide `OsRng` and `JitterRng` on unsupported platforms (#512; fixes #503).


## [0.5.1] - 2018-06-08

### New distributions
- Added Cauchy distribution. (#474, #486)
- Added Pareto distribution. (#495)

### Platform support and `OsRng`
- Remove blanket Unix implementation. (#484)
- Remove Wasm unimplemented stub. (#484)
- Dragonfly BSD: read from `/dev/random`. (#484)
- Bitrig: use `getentropy` like OpenBSD. (#484)
- Solaris: (untested) use `getrandom` if available, otherwise `/dev/random`. (#484)
- Emscripten, `stdweb`: split the read up in chunks. (#484)
- Emscripten, Haiku: don't do an extra blocking read from `/dev/random`. (#484)
- Linux, NetBSD, Solaris: read in blocking mode on first use in `fill_bytes`. (#484)
- Fuchsia, CloudABI: fix compilation (broken in Rand 0.5). (#484)


## [0.5.0] - 2018-05-21

### Crate features and organisation
- Minimum Rust version update: 1.22.0. (#239)
- Create a separate `rand_core` crate. (#288)
- Deprecate `rand_derive`. (#256)
- Add `prelude` (and module reorganisation). (#435)
- Add `log` feature. Logging is now available in `JitterRng`, `OsRng`, `EntropyRng` and `ReseedingRng`. (#246)
- Add `serde1` feature for some PRNGs. (#189)
- `stdweb` feature for `OsRng` support on WASM via stdweb. (#272, #336)

### `Rng` trait
- Split `Rng` in `RngCore` and `Rng` extension trait.
  `next_u32`, `next_u64` and `fill_bytes` are now part of `RngCore`. (#265)
- Add `Rng::sample`. (#256)
- Deprecate `Rng::gen_weighted_bool`. (#308)
- Add `Rng::gen_bool`. (#308)
- Remove `Rng::next_f32` and `Rng::next_f64`. (#273)
- Add optimized `Rng::fill` and `Rng::try_fill` methods. (#247)
- Deprecate `Rng::gen_iter`. (#286)
- Deprecate `Rng::gen_ascii_chars`. (#279)

### `rand_core` crate
- `rand` now depends on new `rand_core` crate (#288)
- `RngCore` and `SeedableRng` are now part of `rand_core`. (#288)
- Add modules to help implementing RNGs `impl` and `le`. (#209, #228)
- Add `Error` and `ErrorKind`. (#225)
- Add `CryptoRng` marker trait. (#273)
- Add `BlockRngCore` trait. (#281)
- Add `BlockRng` and `BlockRng64` wrappers to help implementations. (#281, #325)
- Revise the `SeedableRng` trait. (#233)
- Remove default implementations for `RngCore::next_u64` and `RngCore::fill_bytes`. (#288)
- Add `RngCore::try_fill_bytes`. (#225)

### Other traits and types
- Add `FromEntropy` trait. (#233, #375)
- Add `SmallRng` wrapper. (#296)
- Rewrite `ReseedingRng` to only work with `BlockRngCore` (substantial performance improvement). (#281)
- Deprecate `weak_rng`. Use `SmallRng` instead. (#296)
- Deprecate `AsciiGenerator`. (#279)

### Random number generators
- Switch `StdRng` and `thread_rng` to HC-128. (#277)
- `StdRng` must now be created with `from_entropy` instead of `new`
- Change `thread_rng` reseeding threshold to 32 MiB. (#277)
- PRNGs no longer implement `Copy`. (#209)
- `Debug` implementations no longer show internals. (#209)
- Implement `Clone` for `ReseedingRng`, `JitterRng`, OsRng`. (#383, #384)
- Implement serialization for `XorShiftRng`, `IsaacRng` and `Isaac64Rng` under the `serde1` feature. (#189)
- Implement `BlockRngCore` for `ChaChaCore` and `Hc128Core`. (#281)
- All PRNGs are now portable across big- and little-endian architectures. (#209)
- `Isaac64Rng::next_u32` no longer throws away half the results. (#209)
- Add `IsaacRng::new_from_u64` and `Isaac64Rng::new_from_u64`. (#209)
- Add the HC-128 CSPRNG `Hc128Rng`. (#210)
- Change ChaCha20 to have 64-bit counter and 64-bit stream. (#349)
- Changes to `JitterRng` to get its size down from 2112 to 24 bytes. (#251)
- Various performance improvements to all PRNGs.

### Platform support and `OsRng`
- Add support for CloudABI. (#224)
- Remove support for NaCl. (#225)
- WASM support for `OsRng` via stdweb, behind the `stdweb` feature. (#272, #336)
- Use `getrandom` on more platforms for Linux, and on Android. (#338)
- Use the `SecRandomCopyBytes` interface on macOS. (#322)
- On systems that do not have a syscall interface, only keep a single file descriptor open for `OsRng`. (#239)
- On Unix, first try a single read from `/dev/random`, then `/dev/urandom`. (#338)
- Better error handling and reporting in `OsRng` (using new error type). (#225)
- `OsRng` now uses non-blocking when available. (#225)
- Add `EntropyRng`, which provides `OsRng`, but has `JitterRng` as a fallback. (#235)

### Distributions
- New `Distribution` trait. (#256)
- Add `Distribution::sample_iter` and `Rng::::sample_iter`. (#361)
- Deprecate `Rand`, `Sample` and `IndependentSample` traits. (#256)
- Add a `Standard` distribution (replaces most `Rand` implementations). (#256)
- Add `Binomial` and `Poisson` distributions. (#96)
- Add `Bernoulli` dsitribution. (#411)
- Add `Alphanumeric` distribution. (#279)
- Remove `Closed01` distribution, add `OpenClosed01`. (#274, #420)
- Rework `Range` type, making it possible to implement it for user types. (#274)
- Rename `Range` to `Uniform`. (#395)
- Add `Uniform::new_inclusive` for inclusive ranges. (#274)
- Use widening multiply method for much faster integer range reduction. (#274)
- `Standard` distribution for `char` uses `Uniform` internally. (#274)
- `Standard` distribution for `bool` uses sign test. (#274)
- Implement `Standard` distribution for `Wrapping<T>`. (#436)
- Implement `Uniform` distribution for `Duration`. (#427)


## [0.4.3] - 2018-08-16
### Fixed
- Use correct syscall number for PowerPC (#589)


## [0.4.2] - 2018-01-06
### Changed
- Use `winapi` on Windows
- Update for Fuchsia OS
- Remove dev-dependency on `log`


## [0.4.1] - 2017-12-17
### Added
- `no_std` support


## [0.4.0-pre.0] - 2017-12-11
### Added
- `JitterRng` added as a high-quality alternative entropy source using the
  system timer
- new `seq` module with `sample_iter`, `sample_slice`, etc.
- WASM support via dummy implementations (fail at run-time)
- Additional benchmarks, covering generators and new seq code

### Changed
- `thread_rng` uses `JitterRng` if seeding from system time fails
  (slower but more secure than previous method)

### Deprecated
  - `sample` function deprecated (replaced by `sample_iter`)


## [0.3.20] - 2018-01-06
### Changed
- Remove dev-dependency on `log`
- Update `fuchsia-zircon` dependency to 0.3.2


## [0.3.19] - 2017-12-27
### Changed
- Require `log <= 0.3.8` for dev builds
- Update `fuchsia-zircon` dependency to 0.3
- Fix broken links in docs (to unblock compiler docs testing CI)


## [0.3.18] - 2017-11-06
### Changed
- `thread_rng` is seeded from the system time if `OsRng` fails
- `weak_rng` now uses `thread_rng` internally


## [0.3.17] - 2017-10-07
### Changed
 - Fuchsia: Magenta was renamed Zircon

## [0.3.16] - 2017-07-27
### Added
- Implement Debug for mote non-public types
- implement `Rand` for (i|u)i128
- Support for Fuchsia

### Changed
- Add inline attribute to SampleRange::construct_range.
  This improves the benchmark for sample in 11% and for shuffle in 16%.
- Use `RtlGenRandom` instead of `CryptGenRandom`


## [0.3.15] - 2016-11-26
### Added
- Add `Rng` trait method `choose_mut`
- Redox support

### Changed
- Use `arc4rand` for `OsRng` on FreeBSD.
- Use `arc4random(3)` for `OsRng` on OpenBSD.

### Fixed
- Fix filling buffers 4 GiB or larger with `OsRng::fill_bytes` on Windows


## [0.3.14] - 2016-02-13
### Fixed
- Inline definitions from winapi/advapi32, wich decreases build times


## [0.3.13] - 2016-01-09
### Fixed
- Compatible with Rust 1.7.0-nightly (needed some extra type annotations)


## [0.3.12] - 2015-11-09
### Changed
- Replaced the methods in `next_f32` and `next_f64` with the technique described
  Saito & Matsumoto at MCQMC'08. The new method should exhibit a slightly more
  uniform distribution.
- Depend on libc 0.2

### Fixed
- Fix iterator protocol issue in `rand::sample`


## [0.3.11] - 2015-08-31
### Added
- Implement `Rand` for arrays with n <= 32


## [0.3.10] - 2015-08-17
### Added
- Support for NaCl platforms

### Changed
- Allow `Rng` to be `?Sized`, impl for `&mut R` and `Box<R>` where `R: ?Sized + Rng`


## [0.3.9] - 2015-06-18
### Changed
- Use `winapi` for Windows API things

### Fixed
- Fixed test on stable/nightly
- Fix `getrandom` syscall number for aarch64-unknown-linux-gnu


## [0.3.8] - 2015-04-23
### Changed
- `log` is a dev dependency

### Fixed
- Fix race condition of atomics in `is_getrandom_available`


## [0.3.7] - 2015-04-03
### Fixed
- Derive Copy/Clone changes


## [0.3.6] - 2015-04-02
### Changed
- Move to stable Rust!


## [0.3.5] - 2015-04-01
### Fixed
- Compatible with Rust master


## [0.3.4] - 2015-03-31
### Added
- Implement Clone for `Weighted`

### Fixed
- Compatible with Rust master


## [0.3.3] - 2015-03-26
### Fixed
- Fix compile on Windows


## [0.3.2] - 2015-03-26


## [0.3.1] - 2015-03-26
### Fixed
- Fix compile on Windows


## [0.3.0] - 2015-03-25
### Changed
- Update to use log version 0.3.x


## [0.2.1] - 2015-03-22
### Fixed
- Compatible with Rust master
- Fixed iOS compilation


## [0.2.0] - 2015-03-06
### Fixed
- Compatible with Rust master (move from `old_io` to `std::io`)


## [0.1.4] - 2015-03-04
### Fixed
- Compatible with Rust master (use wrapping ops)


## [0.1.3] - 2015-02-20
### Fixed
- Compatible with Rust master

### Removed
- Removed Copy implementations from RNGs


## [0.1.2] - 2015-02-03
### Added
- Imported functionality from `std::rand`, including:
  - `StdRng`, `SeedableRng`, `TreadRng`, `weak_rng()`
  - `ReaderRng`: A wrapper around any Reader to treat it as an RNG.
- Imported documentation from `std::rand`
- Imported tests from `std::rand`


## [0.1.1] - 2015-02-03
### Added
- Migrate to a cargo-compatible directory structure.

### Fixed
- Do not use entropy during `gen_weighted_bool(1)`


## [Rust 0.12.0] - 2014-10-09
### Added
- Impl Rand for tuples of arity 11 and 12
- Include ChaCha pseudorandom generator
- Add `next_f64` and `next_f32` to Rng
- Implement Clone for PRNGs

### Changed
- Rename `TaskRng` to `ThreadRng` and `task_rng` to `thread_rng` (since a
  runtime is removed from Rust).

### Fixed
- Improved performance of ISAAC and ISAAC64 by 30% and 12 % respectively, by
  informing the optimiser that indexing is never out-of-bounds.

### Removed
- Removed the Deprecated `choose_option`


## [Rust 0.11.0] - 2014-07-02
### Added
- document when to use `OSRng` in cryptographic context, and explain why we use `/dev/urandom` instead of `/dev/random`
- `Rng::gen_iter()` which will return an infinite stream of random values
- `Rng::gen_ascii_chars()` which will return an infinite stream of random ascii characters

### Changed
- Now only depends on libcore!
- Remove `Rng.choose()`, rename `Rng.choose_option()` to `.choose()`
- Rename OSRng to OsRng
- The WeightedChoice structure is no longer built with a `Vec<Weighted<T>>`,
  but rather a `&mut [Weighted<T>]`. This means that the WeightedChoice
  structure now has a lifetime associated with it.
- The `sample` method on `Rng` has been moved to a top-level function in the
  `rand` module due to its dependence on `Vec`.

### Removed
- `Rng::gen_vec()` was removed. Previous behavior can be regained with
  `rng.gen_iter().take(n).collect()`
- `Rng::gen_ascii_str()` was removed. Previous behavior can be regained with
  `rng.gen_ascii_chars().take(n).collect()`
- {IsaacRng, Isaac64Rng, XorShiftRng}::new() have all been removed. These all
  relied on being able to use an OSRng for seeding, but this is no longer
  available in librand (where these types are defined). To retain the same
  functionality, these types now implement the `Rand` trait so they can be
  generated with a random seed from another random number generator. This allows
  the stdlib to use an OSRng to create seeded instances of these RNGs.
- Rand implementations for `Box<T>` and `@T` were removed. These seemed to be
  pretty rare in the codebase, and it allows for librand to not depend on
  liballoc.  Additionally, other pointer types like Rc<T> and Arc<T> were not
  supported.
- Remove a slew of old deprecated functions


## [Rust 0.10] - 2014-04-03
### Changed
- replace `Rng.shuffle's` functionality with `.shuffle_mut`
- bubble up IO errors when creating an OSRng

### Fixed
- Use `fill()` instead of `read()`
- Rewrite OsRng in Rust for windows

## [0.10-pre] - 2014-03-02
### Added
- Seperate `rand` out of the standard library
