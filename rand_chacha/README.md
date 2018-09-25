# rand_chacha

[![Build Status](https://travis-ci.org/rust-random/rand.svg)](https://travis-ci.org/rust-random/rand)
[![Build Status](https://ci.appveyor.com/api/projects/status/github/rust-random/rand?svg=true)](https://ci.appveyor.com/project/rust-random/rand)
[![Latest version](https://img.shields.io/crates/v/rand_chacha.svg)](https://crates.io/crates/rand_chacha)
[![Documentation](https://docs.rs/rand_chacha/badge.svg)](https://docs.rs/rand_chacha)
[![Minimum rustc version](https://img.shields.io/badge/rustc-1.22+-yellow.svg)](https://github.com/rust-random/rand#rust-version-requirements)
[![License](https://img.shields.io/crates/l/rand_chacha.svg)](https://github.com/rust-random/rand/tree/master/rand_chacha#license)

A cryptographically secure random number generator that uses the ChaCha
algorithm.

ChaCha is a stream cipher designed by Daniel J. Bernstein[^1], that we use
as an RNG. It is an improved variant of the Salsa20 cipher family, which was
selected as one of the "stream ciphers suitable for widespread adoption" by
eSTREAM[^2].

Documentation:
[master branch](https://rust-random.github.io/rand/rand_chacha/index.html),
[by release](https://docs.rs/rand_chacha)

[Changelog](CHANGELOG.md)

[rand]: https://crates.io/crates/rand
[^1]: D. J. Bernstein, [*ChaCha, a variant of Salsa20*](
      https://cr.yp.to/chacha.html)

[^2]: [eSTREAM: the ECRYPT Stream Cipher Project](
      http://www.ecrypt.eu.org/stream/)


## Crate Features

`rand_chacha` is `no_std` compatible. It does not require any functionality
outside of the `core` lib, thus there are no features to configure.


# License

`rand_chacha` is distributed under the terms of both the MIT license and the
Apache License (Version 2.0).

See [LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT), and
[COPYRIGHT](COPYRIGHT) for details.
