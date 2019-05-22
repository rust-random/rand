# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.2.0] - 2019-05-??
Fix `seed_from_u64(0)` for `Xoroshiro64StarStar` and `Xoroshiro64Star`. This
breaks value stability for these generators if initialized with `seed_from_u64`.

## [0.1.0] - 2019-01-04
Initial release.
