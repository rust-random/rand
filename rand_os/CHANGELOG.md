# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.2.2] - 2019-08-28
### Changed
- `OsRng` added to `rand_core`, rendering this crate deprecated (#863)

## [0.2.1] - 2019-08-08
### Fixed
- Fix `no_std` support.

## [0.2.0] - 2019-06-06
### Changed
- Minimum Supported Rust Version has changed to 1.32.
- Replaced implementation with a backwards-compatible shim around
[getrandom](https://crates.io/crates/getrandom).

## [0.1.3] - 2019-03-05
### Fixed
- Fix support for Illumos (#730)
- Fix deprecation warnings from atomic init (#739)

## [0.1.2] - 2019-01-28
### Changed
- Fuchsia: Replaced fuchsia-zircon with fuchsia-cprng

## [0.1.1] - 2019-01-08
### Added
- Add support for x86_64-fortanix-unknown-sgx target (#670)

## [0.1.0] - 2019-01-04
Initial release.
