# rand_distr

[![Build Status](https://travis-ci.org/rust-random/rand.svg?branch=master)](https://travis-ci.org/rust-random/rand)
[![Build Status](https://ci.appveyor.com/api/projects/status/github/rust-random/rand?svg=true)](https://ci.appveyor.com/project/rust-random/rand)
[![Latest version](https://img.shields.io/crates/v/rand_distr.svg)](https://crates.io/crates/rand_distr)
[[![Book](https://img.shields.io/badge/book-master-yellow.svg)](https://rust-random.github.io/book/)
[![API](https://img.shields.io/badge/api-master-yellow.svg)](https://rust-random.github.io/rand/rand_distr)
[![API](https://docs.rs/rand_distr/badge.svg)](https://docs.rs/rand_distr)
[![Minimum rustc version](https://img.shields.io/badge/rustc-1.32+-lightgray.svg)](https://github.com/rust-random/rand#rust-version-requirements)

Implements a full suite of random number distributions sampling routines.

This crate is a super-set of the [rand::distributions] module, including support
for sampling from Beta, Binomial, Cauchy, ChiSquared, Dirichlet, exponential,
Fisher F, Gamma, Log-normal, Normal, Pareto, Poisson, StudentT, Triangular and
Weibull distributions, as well as sampling points from the unit circle and unit
sphere surface.

It is worth mentioning the [statrs] crate which provides similar functionality
along with various support functions, including PDF and CDF computation. In
contrast, this `rand_distr` crate focusses on sampling from distributions.

Unlike most Rand crates, `rand_distr` does not currently support `no_std`.

Links:

-   [API documentation (master)](https://rust-random.github.io/rand/rand_distr)
-   [API documentation (docs.rs)](https://docs.rs/rand_distr)
-   [Changelog](CHANGELOG.md)
-   [The Rand project](https://github.com/rust-random/rand)


[statrs]: https://github.com/boxtown/statrs
[rand::distributions]: https://rust-random.github.io/rand/rand/distributions/index.html

## License

`rand_distr` is distributed under the terms of both the MIT license and the
Apache License (Version 2.0).

See [LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT), and
[COPYRIGHT](COPYRIGHT) for details.
