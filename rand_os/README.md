# rand_os

[![Build Status](https://travis-ci.org/rust-random/rand.svg?branch=master)](https://travis-ci.org/rust-random/rand)
[![Build Status](https://ci.appveyor.com/api/projects/status/github/rust-random/rand?svg=true)](https://ci.appveyor.com/project/rust-random/rand)
[![Latest version](https://img.shields.io/crates/v/rand_os.svg)](https://crates.io/crates/rand_os)
[![Book](https://img.shields.io/badge/book-master-yellow.svg)](https://rust-random.github.io/book/)
[![API](https://img.shields.io/badge/api-master-yellow.svg)](https://rust-random.github.io/rand/rand_os)
[![API](https://docs.rs/rand_os/badge.svg)](https://docs.rs/rand_os)
[![Minimum rustc version](https://img.shields.io/badge/rustc-1.32+-lightgray.svg)](https://github.com/rust-random/rand#rust-version-requirements)

A random number generator that retrieves randomness straight from the
operating system.

**This crate is deprecated:** `OsRng` is available in `rand_core` since version 0.5.1.

This crate provides `OsRng` as a shim around
[getrandom](https://crates.io/crates/getrandom)
implementing `RngCore` from [rand_core](https://crates.io/crates/rand_core).

Note: the `rand` crate provides an equivalent `OsRng`; the two implementations
are equivalent, though distinct types.

Links:

-   [API documentation (master)](https://rust-random.github.io/rand/rand_os)
-   [API documentation (docs.rs)](https://docs.rs/rand_os)
-   [Changelog](https://github.com/rust-random/rand/blob/master/rand_os/CHANGELOG.md)

## License

`rand_os` is distributed under the terms of both the MIT license and the
Apache License (Version 2.0).

See [LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT), and
[COPYRIGHT](COPYRIGHT) for details.
