# Rand Documentation

Also see the [main project readme](../README.md).

## Learning Rand

TODO. In the mean-time, we have some learning resources within the API
documentation.

The following example programs may be of interest:

- [examples/monte-carlo.rs](https://github.com/rust-lang-nursery/rand/blob/master/examples/monte-carlo.rs)
- [examples/monty-hall.rs](https://github.com/rust-lang-nursery/rand/blob/master/examples/monty-hall.rs)

## References

API documentation can be found:

- [`rand` API on docs.rs](https://docs.rs/rand/)
- [`rand_core` API on docs.rs](https://docs.rs/rand_core/)
- [self-published API on github.io](https://rust-lang-nursery.github.io/rand/rand/index.html) (latest code in master branch)
- by running `cargo doc --no-deps --all --all-features`

## Project policies

### Open Participation

This project is open to contributions from anyone, with the main criteria of
review being correctness, utility, project scope, and good documentation. Where
correctness is less obvious (PRNGs and some type-conversion algorithms),
additional criteria apply (see below).

Additionally we welcome feedback in the form of bug reports, feature requests
(preferably with motivation and consideration for the scope of the project),
code reviews, and input on current topics of discussion.

Since we must sometimes reject new features in order to limit the project's
scope, you may wish to ask first before writing a new feature.

### Stability

TODO

### Project Scope

TODO

### Code style

We do not currently have many policies on style other than:

- neat and consistent
- minimise changes which are purely stylistic, or move to a separate commit

Rand does **make use of `unsafe`**, both for performance and out of necessity.
We consider this acceptable so long as correctness is easy to verify.
In order to make this as simple as possible,
we prefer that all parameters affecting safety of `unsafe` blocks are checked or
prepared close to the `unsafe` code,
and wherever possible within the same function (thus making the function safe).

### New PRNG Algorithms

TODO
