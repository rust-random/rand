rand
====

Core functionality for the [rand] library.

This crate contains the core trait, `Rng`, and some extension traits. This
should be sufficient for libraries publishing an RNG type, but most users should
prefer to use the [rand] crate.

[Documentation](https://docs.rs/rand)


## Status

This crate is experimental, provided as part of the [rand crate refactor]. Users
should be wary of depending on this crate at this time; breaking changes should
be expected and contents will conflict with those of the current published
version of rand (0.3.x).

# License

`rand` is primarily distributed under the terms of both the MIT
license and the Apache License (Version 2.0), with portions covered by various
BSD-like licenses.

See LICENSE-APACHE, and LICENSE-MIT for details.

[rand]: ..
[rand crate refactor]: https://github.com/rust-lang/rfcs/pull/2106
