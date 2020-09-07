# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]
- New `Beta` sampling algorithm for improved performance and accuracy (#1000)

## [0.3.0] - 2020-08-25
- Move alias method for `WeightedIndex` from `rand` (#945)
- Rename `WeightedIndex` to `WeightedAliasIndex` (#1008)
- Replace custom `Float` trait with `num-traits::Float` (#987)
- Enable `no_std` support via `num-traits` math functions (#987)
- Remove `Distribution<u64>` impl for `Poisson` (#987)
- Tweak `Dirichlet` and `alias_method` to use boxed slice instead of `Vec` (#987)
- Use whitelist for package contents, reducing size by 5kb (#983)
- Add case `lambda = 0` in the parametrization of `Exp` (#972)
- Implement inverse Gaussian distribution (#954)
- Reformatting and use of `rustfmt::skip` (#926)
- All error types now implement `std::error::Error` (#919)
- Re-exported `rand::distributions::BernoulliError` (#919)
- Add value stability tests for distributions (#891)

## [0.2.2] - 2019-09-10
- Fix version requirement on rand lib (#847)
- Clippy fixes & suppression (#840)

## [0.2.1] - 2019-06-29
- Update dependency to support Rand 0.7
- Doc link fixes

## [0.2.0] - 2019-06-06
- Remove `new` constructors for zero-sized types
- Add Pert distribution
- Fix undefined behavior in `Poisson`
- Make all distributions return `Result`s instead of panicking
- Implement `f32` support for most distributions
- Rename `UnitSphereSurface` to `UnitSphere`
- Implement `UnitBall` and `UnitDisc`

## [0.1.0] - 2019-06-06
Initial release. This is equivalent to the code in `rand` 0.6.5.
