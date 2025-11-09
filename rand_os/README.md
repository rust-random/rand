# Rand OS

[![Test Status](https://github.com/rust-random/rand/actions/workflows/test.yml/badge.svg?event=push)](https://github.com/rust-random/rand/actions)
[![Crate](https://img.shields.io/crates/v/rand_os.svg)](https://crates.io/crates/rand_os)
[![Book](https://img.shields.io/badge/book-master-yellow.svg)](https://rust-random.github.io/book/)
[![API](https://docs.rs/rand_os/badge.svg)](https://docs.rs/rand_os)

Provides [`OsRng`] over [rand_core] and [getrandom]. You don't need this if you use [rand], but it's also pretty harmless to depend on both crates since [`OsRng`] is just a shim over [getrandom].

## Crate Features

With `std`, the error type implements [`std::error::Error`].

### WebAssembly support

The [WASI](https://github.com/WebAssembly/WASI/tree/main) and Emscripten targets are directly supported.

The `wasm32-unknown-unknown` target is not *automatically* supported. To enable support for this target, enable the `wasm_js` feature. **Warning: this feature can break `wasm32-unknown-unknown` builds on non-web platforms!** Do not enable this feature in libraries unless you are *sure* you do not want to support non-web Wasm32 platforms.

For more information, refer to
[`getrandom` documentation for WebAssembly](https://docs.rs/getrandom/latest/getrandom/#webassembly-support).

# License

Rand is distributed under the terms of both the MIT license and the
Apache License (Version 2.0).

See [LICENSE-APACHE](https://github.com/rust-random/rand/blob/master/LICENSE-APACHE) and [LICENSE-MIT](https://github.com/rust-random/rand/blob/master/LICENSE-MIT), and
[COPYRIGHT](https://github.com/rust-random/rand/blob/master/COPYRIGHT) for details.

[getrandom]: https://crates.io/crates/getrandom
[rand]: https://crates.io/crates/rand
[rand_core]: https://crates.io/crates/rand_core
[`OsRng`]: https://docs.rs/rand_os/latest/rand_os/struct.OsRng.html
[`std::error::Error`]: https://doc.rust-lang.org/std/error/trait.Error.html
