# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]
### Changed
- Bump MSRV to 1.85 and edition to 2024 (#1671)
- Remove feature `os_rng` (#1674)

## [0.9.0] - 2025-01-27
### Dependencies and features
- Update to `rand_core` v0.9.0 (#1558)
- Feature `std` now implies feature `rand_core/std` (#1153)
- Rename feature `serde1` to `serde` (#1477)
- Rename feature `getrandom` to `os_rng` (#1537)

### Other changes
- Remove usage of `unsafe` in `fn generate` (#1181) then optimise for AVX2 (~4-7%) (#1192)
- Revise crate docs (#1454)

## [0.3.1] - 2021-06-09
- add getters corresponding to existing setters: `get_seed`, `get_stream` (#1124)
- add serde support, gated by the `serde1` feature (#1124)
- ensure expected layout via `repr(transparent)` (#1120)

## [0.3.0] - 2020-12-08
- Bump `rand_core` version to 0.6.0
- Bump MSRV to 1.36 (#1011)
- Remove usage of deprecated feature "simd" of `ppv-lite86` (#979), then revert
  this change (#1023) since SIMD is only enabled by default from `ppv-lite86 v0.2.10`
- impl PartialEq+Eq for ChaChaXRng and ChaChaXCore (#979)
- Fix panic on block counter wrap that was occurring in debug builds (#980)

## [0.2.2] - 2020-03-09
- Integrate `c2-chacha`, reducing dependency count (#931)
- Add CryptoRng to ChaChaXCore (#944)

## [0.2.1] - 2019-07-22
- Force enable the `simd` feature of `c2-chacha` (#845)

## [0.2.0] - 2019-06-06
- Rewrite based on the much faster `c2-chacha` crate (#789)

## [0.1.1] - 2019-01-04
- Disable `i128` and `u128` if the `target_os` is `emscripten` (#671: work-around Emscripten limitation)
- Update readme and doc links

## [0.1.0] - 2018-10-17
- Pulled out of the Rand crate

[Unreleased]: https://github.com/rust-random/rand/compare/0.9.0...HEAD
[0.9.0]: https://github.com/rust-random/rand/compare/rand_chacha-0.3.1...0.9.0
[0.3.1]: https://github.com/rust-random/rand/compare/rand_chacha-0.3.0...rand_chacha-0.3.1
[0.3.0]: https://github.com/rust-random/rand/compare/rand_chacha-0.2.2...rand_chacha-0.3.0
[0.2.2]: https://github.com/rust-random/rand/compare/rand_chacha-0.2.1...rand_chacha-0.2.2
[0.2.1]: https://github.com/rust-random/rand/compare/rand_chacha-0.2.0...rand_chacha-0.2.1
[0.2.0]: https://github.com/rust-random/rand/compare/rand_chacha-0.1.1...rand_chacha-0.2.0
[0.1.1]: https://github.com/rust-random/rand/compare/rand_chacha-0.1.0...rand_chacha-0.1.1
[0.1.0]: https://github.com/rust-random/rand/compare/a55ba3feb49062ea8dec75c034d796f6e3f763ae...rand_chacha-0.1.0
