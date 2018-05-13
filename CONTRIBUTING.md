# Contributing to Rand

Thank you for your interest in contributing to Rand!

The following is a list of notes and tips for when you want to contribute to
Rand with a pull request.

If you want to make major changes, it is usually best to open an issue to
discuss the idea first.

Rand doesn't (yet) use rustfmt. It is best to follow the style of the
surrounding code, and try to keep an 80 character line limit.


## Documentation

We especially welcome documentation PRs.

As of Rust 1.25 there are differences in how stable and nightly render
documentation links. Make sure it works on stable, then nightly should be good
too. One Travis CI build checks for dead links using `cargo-deadlinks`. If you
want to run the check locally:
```sh
cargo install cargo-deadlinks
# It is recommended to remove left-over files from previous compilations
rm -rf /target/doc
cargo doc --no-deps
cargo deadlinks --dir target/doc
```

When making changes to code examples in the documentation, make sure they build
with:
```sh
cargo test --doc
```

A helpful command to rebuild documentation automatically on save (only works on
Linux):
```
while inotifywait -r -e close_write src/ rand_core/; do cargo doc; done
```


## Testing

Rand already contains a number of unit tests, but could use more. Also the
existing ones could use clean-up. Any work on the tests is appreciated.

Not every change or new bit of functionality requires tests, but if you can
think of a test that adds value, please add it.

Depending on the code you change, test with one of:
```sh
cargo test
cargo test --package rand_core
# Test log, serde and 128-bit support
cargo test --features serde1,log,nightly
```

We want to be able to not only run the unit tests with `std` available, but also
without. Because `thread_rng()` and `FromEntropy` are not available without the
`std` feature, you may have to disable a new test with `#[cfg(feature="std")]`.
In other cases using `::test::rng` with a constant seed is a good option:
```rust
let mut rng = ::test::rng(528); // just pick some number
```

Only the unit tests should work in `no_std` mode, we don't want to complicate
the doc-tests. Run the tests with:
```sh
# Test no_std support
cargo test --lib --no-default-features
cargo test --package rand_core --no-default-features

# Test no_std+alloc support; requires nightly
cargo test --lib --no-default-features --features alloc
```


## Benchmarking

A lot of code in Rand is performance-sensitive, most of it is expected to be
used in hot loops in some libraries/applications. If you change code in the
`rngs`, `prngs` or `distributions` modules, especially when you see an 'obvious
cleanup', make sure the benchmarks do not regress. It is nice to report the
benchmark results in the PR (or to report nothing's changed).

```sh
# Benchmarks (requires nightly)
cargo bench
# Some benchmarks have a faster path with i128_support
cargo bench --features=nightly
```
