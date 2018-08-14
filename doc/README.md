# Rand Documentation

Also see the [main project readme](../README.md).

## Learning Rand

TODO. In the mean-time, we have some learning resources within the API
documentation.

The following example programs may be of interest:

- [examples/monte-carlo.rs](https://github.com/rust-random/rand/blob/master/examples/monte-carlo.rs)
- [examples/monty-hall.rs](https://github.com/rust-random/rand/blob/master/examples/monty-hall.rs)

## References

API documentation can be found:

- [`rand` API on docs.rs](https://docs.rs/rand/)
- [`rand_core` API on docs.rs](https://docs.rs/rand_core/)
- [self-published API on github.io](https://rust-random.github.io/rand/rand/index.html) (latest code in master branch)
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

### Stability and Portability

We try to follow [semver rules](https://docs.npmjs.com/misc/semver) regarding
API-breaking changes and `MAJOR.MINOR.PATCH` versions:

-   New *patch* versions should not include API-breaking changes or major new
    features
-   Before 1.0, *minor* versions may include API breaking changes. After 1.0
    they should not.
-   We may make pre-releases like `0.5.0-pre.0`. In this case:
    
    -   although these are public versions, they are not used by default unless
        opting into using a pre-release on the specific `MAJOR.MINOR.PATCH`
        version
    -   pre-releases are considered semantically less than their final release
        (e.g. Cargo may automatically upgrade from `0.5.0-pre.0` to `0.5.0`)
    -   all pre-release versions are unstable and may make any change
    -   we make no commitment to support users of pre-releases

Additionally, we must also consider *value-breaking changes* and *portability*.
A function is *value-stable* if, given the same inputs:

-   it is portable (produces the same results on all platforms)
-   changing the output value for some input in a new library version is
    considered a breaking change

Note that some Rand functionality is supposed to be value stable, and some
functionality is supposed to be non-deterministic (i.e. depend on something
external). Some functionality may be deterministic but not value-stable.

A trait should define which of its functions are expected to be value-stable.
An implementation of a trait must meet those stability requirements, unless the
object for which the trait is implemented is explicitly not value-stable.
As an example, `SeedableRng::from_seed` is required to be value-stable, but
`SeedableRng::from_rng` is not. RNGs implementing the trait are value-stable
when they guarantee `SeedableRng::from_seed` is value-stable, while
`SeedableRng::from_rng` may receive optimisations.

Before 1.0, we allow any new *minor* version to break value-stability, though
we do expect such changes to be mentioned in the changelog. Post 1.0 we have
not yet determined exact stability rules.

Additionally, we expect patch versions not to change the output of any
deterministic functions, even if not value-stable (this is not a hard
requirement, but exceptions should be noted in the changelog).

Defining which parts of Rand are value-stable is still in progress. Many parts
of `rand_core` have some documentation on value-stability.

### Project Scope

The `rand_core` library has the following scope:

-   the core traits which RNGs may implement
-   tools for implementing these traits

The `rand` library has the following scope:

-   re-export all parts of `rand_core` applicable to end users
-   an interface to request entropy from an external source
-   hooks to provide entropy from several platform-specific sources
-   traits covering common RNG functionality
-   some PRNGs, notably `StdRng` and `SmallRng`
-   `thread_rng` auto-seeding source of randomness
-   conversion of random bits to common types and uses
-   shuffling and sampling from sequences
-   sampling from various random number distributions

Note: the scope of the project and above libraries may change. We are currently
discussing moving PRNGs (#431) and distributions (#290) to other libraries or
projects.

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

The Rand library includes several pseudo-random number generators, and we have
received several requests to adopt new algorithms into the library. We must
consider such requests in regards to several things:

-   whether the PRNG is cryptographically secure, and if so, how trustworthy
    such claims are
-   statistical quality of output
-   performance and features of the generator
-   scope of the project
-   reception and third-party review of the algorithm

In general, we expect the following, though we may make exceptions:

-   the author of the algorithm to publish an article of some type (e.g.
    a scientific article or web page) introducing the new algorithm and
    discussing its utility, strengths and weaknesses
-   review of statistical quality and any special features by third parties
-   good performance in automated test suites like PractRand and TestU01
    (unless for some reason this is not expected, e.g. a mock generator)
