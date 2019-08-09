# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.2.1] - 2019-08-16
### Changed
- `TimerError` changed to `repr(u32)` (#864)
- `TimerError` enum values all increased by `1<<30` to match new `rand_core::Error` range (#864)

## [0.2.0] - 2019-06-06
- Bump `rand_core` version
- Support new `Error` type in `rand_core` 0.5
- Remove CryptoRng trait bound (#699, #814)
- Enable doc-testing of README

## [0.1.4] - 2019-05-02
- Change error conversion code to partially fix #738

## [0.1.3] - 2019-02-05
- Use libc in `no_std` mode to fix #723

## [0.1.2] - 2019-01-31
- Fix for older rustc compilers on Windows (#722)

## [0.1.1] - 2019-01-29
- Fix for older rustc compilers on Mac OSX / iOS (#720)
- Misc. doc fixes

## [0.1.0] - 2019-01-24
Initial release.
