# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.4.0] - 2019-09-03
- Add xoshiro128++, 256++ and 512++ variants
- Add xoroshiro128++ variant
- Add `long_jump` method to RNGs missing it
- Update xoshiro128** to version 1.1, breaking value stability

## [0.3.1] - 2019-08-06
- Drop `byteorder`-dependency in favor of `stdlib`-implementation.

## [0.3.0] - 2019-06-12
- Bump minor crate version since rand_core bump is a breaking change
- Switch to Edition 2018

## [0.2.1] - 2019-06-06 - yanked
- Bump `rand_core` version
- Document crate features in README

## [0.2.0] - 2019-05-28
- Fix `seed_from_u64(0)` for `Xoroshiro64StarStar` and `Xoroshiro64Star`. This
  breaks value stability for these generators if initialized with `seed_from_u64`.
- Implement Serde support.

## [0.1.0] - 2019-01-04
Initial release.
