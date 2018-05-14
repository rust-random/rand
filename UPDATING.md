# Update Guide

This guide gives a few more details than the [changelog], in particular giving
guidance on how to use new features and migrate away from old ones.

[changelog]: CHANGELOG.md

## Rand 0.5

The 0.5 release has quite significant changes over the 0.4 release; as such,
it may be worth reading through the following coverage of breaking changes.
This release also contains many optimisations, which are not detailed below.

### Crates

We have a new crate: `rand_core`! This crate houses some important traits,
`RngCore`, `BlockRngCore`, `SeedableRng` and `CryptoRng`, the error types, as
well as two modules with helpers for implementations: `le` and `impls`. It is
recommended that implementations of generators use the `rand_core` crate while
other users use only the `rand` crate, which re-exports most parts of `rand_core`.

The `rand_derive` crate has been deprecated due to very low usage and
deprecation of `Rand`.

### Features

Several new Cargo feature flags have been added:

-   `alloc`, used without `std`, allows use of `Box` and `Vec`
-   `serde1` adds serialization support to some PRNGs
-   `log` adds logging in a few places (primarily to `OsRng` and `JitterRng`)

### `Rng` and friends (core traits)

`Rng` trait has been split into two traits, a "back end" `RngCore` (implemented
by generators) and a "front end" `Rng` implementing all the convenient extension
methods.

Implementations of generators must `impl RngCore` instead. Usage of `rand_core`
for implementations is encouraged; the `rand_core::{le, impls}` modules may
prove useful.

Users of `Rng` *who don't need to implement it* won't need to make so many
changes; often users can forget about `RngCore` and only import `Rng`. Instead
of `RngCore::next_u32()` / `next_u64()` users should prefer `Rng::gen()`, and
instead of `RngCore::fill_bytes(dest)`, `Rng::fill(dest)` can be used.

#### `Rng` / `RngCore` methods

To allow error handling from fallible sources (e.g. `OsRng`), a new
`RngCore::try_fill_bytes` method has been added; for example `EntropyRng` uses
this mechanism to fall back to `JitterRng` if `OsRng` fails, and various
handlers produce better error messages.
As before, the other methods will panic on failure, but since these are usually
used with algorithmic generators which are usually infallible, this is
considered an appropriate compromise.

A few methods from the old `Rng` have been removed or deprecated:

-   `next_f32` and `next_f64`; these are no longer implementable by generators;
    use `gen` instead
-   `gen_iter`; users may instead use standard iterators with closures:
    `::std::iter::repeat(()).map(|()| rng.gen())`
-   `gen_ascii_chars`; use `repeat` as above and `rng.sample(Alphanumeric)`
-   `gen_weighted_bool(n)`; use `gen_bool(1.0 / n)` instead

`Rng` has a few new methods:

-   `sample(distr)` is a shortcut for `distr.sample(rng)` for any `Distribution`
-   `gen_bool(p)` generates a boolean with probability `p` of being true
-   `fill` and `try_fill`, corresponding to `fill_bytes` and `try_fill_bytes`
    respectively (i.e. the only difference is error handling); these can fill
    and integer slice / array directly, and provide better performance
    than `gen()`

#### Constructing PRNGs

##### New randomly-initialised PRNGs

A new trait has been added: `FromEntropy`. This is automatically implemented for
any type supporting `SeedableRng`, and provides construction from fresh, strong
entropy:

```rust
use rand::{ChaChaRng, FromEntropy};

let mut rng = ChaChaRng::from_entropy();
```

##### Seeding PRNGs

The `SeedableRng` trait has been modified to include the seed type via an
associated type (`SeedableRng::Seed`) instead of a template parameter
(`SeedableRng<Seed>`). Additionally, all PRNGs now seed from a byte-array
(`[u8; N]` for some fixed N). This allows generic handling of PRNG seeding
which was not previously possible.

PRNGs are no longer constructed from other PRNGs via `Rand` support / `gen()`,
but through `SeedableRng::from_rng`, which allows error handling and is
intentionally explicit.

`SeedableRng::reseed` has been removed since it has no utility over `from_seed`
and its performance advantage is questionable.

Implementations of `SeedableRng` may need to change their `Seed` type to a
byte-array; this restriction has been made to ensure portable handling of
Endianness. Helper functions are available in `rand_core::le` to read `u32` and
`u64` values from byte arrays.

#### Block-based PRNGs

rand_core has a new helper trait, `BlockRngCore`, and implementation,
`BlockRng`. These are for use by generators which generate a block of random
data at a time instead of word-sized values. Using this trait and implementation
has two advantages: optimised `RngCore` methods are provided, and the PRNG can
be used with `ReseedingRng` with very low overhead.

#### Cryptographic RNGs

A new trait has been added: `CryptoRng`. This is purely a marker trait to
indicate which generators should be suitable for cryptography, e.g.
`fn foo<R: Rng + CryptoRng>(rng: &mut R)`. *Suitability for cryptographic
use cannot be guaranteed.*

### Error handling

A new `Error` type has been added, designed explicitly for no-std compatibility,
simplicity, and enough flexibility for our uses (carrying a `cause` when
possible):
```rust
pub struct Error {
    pub kind: ErrorKind,
    pub msg: &'static str,
    // some fields omitted
}
```
The associated `ErrorKind` allows broad classification of errors into permanent,
unexpected, transient and not-yet-ready kinds.

The following use the new error type:

-   `RngCore::try_fill_bytes`
-   `Rng::try_fill`
-   `OsRng::new`
-   `JitterRng::new`

### External generators

We have a new generator, `EntropyRng`, which wraps `OsRng` and `JitterRng`
(preferring to use the former, but falling back to the latter if necessary).
This allows easy construction with fallback via `SeedableRng::from_rng`,
e.g. `IsaacRng::from_rng(EntropyRng::new())?`. This is equivalent to using
`FromEntropy` except for error handling.

It is recommended to use `EntropyRng` over `OsRng` to avoid errors on platforms
with broken system generator, but it should be noted that the `JitterRng`
fallback is very slow.

### PRNGs

*Pseudo-Random Number Generators* (i.e. deterministic algorithmic generators)
have had a few changes since 0.4, and are now housed in the `prng` module
(old names remain temporarily available for compatibility; eventually these
generators will likely be housed outside the `rand` crate).

All PRNGs now do not implement `Copy` to prevent accidental copying of the
generator's state (and thus repetitions of generated values). Explicit cloning
via `Clone` is still available. All PRNGs now have a custom implementation of
`Debug` which does not print any internal state; this helps avoid accidentally
leaking cryptographic generator state in log files. External PRNG
implementations are advised to follow this pattern (see also doc on `RngCore`).

`SmallRng` has been added as a wrapper, currently around `XorShiftRng` (but
likely another algorithm soon). This is for uses where small state and fast
initialisation are important but cryptographic strength is not required.
(Actual performance of generation varies by benchmark; dependending on usage
this may or may not be the fastest algorithm, but will always be fast.)

#### `ReseedingRng`

The `ReseedingRng` wrapper has been signficantly altered to reduce overhead.
Unfortunately the new `ReseedingRng` is not compatible with all RNGs, but only
those using `BlockRngCore`.

#### ISAAC PRNGs

The `IsaacRng` and `Isaac64Rng` PRNGs now have an additional construction
method: `new_from_u64(seed)`. 64 bits of state is insufficient for cryptography
but may be of use in simulations and games. This will likely be superceeded by
a method to construct any PRNG from any hashable object in the future.

#### HC-128

This is a new cryptographic generator, selected as one of the "stream ciphers
suitable for widespread adoption" by eSTREAM. This is now the default
cryptographic generator, used by `StdRng` and `thread_rng()`.

### Helper functions/traits

The `Rand` trait has been deprecated. Instead, users are encouraged to use
`Standard` which is a real distribution and supports the same sampling as
`Rand`. `Rng::gen()` now uses `Standard` and should work exactly as before.
See the documentation of the `distributions` module on how to implement
`Distribution<T>` for `Standard` for user types `T`

`weak_rng()` has been deprecated; use `SmallRng::from_entropy()` instead.

### Distributions

The `Sample` and `IndependentSample` traits have been replaced by a single
trait, `Distribution`. This is largely equivalent to `IndependentSample`, but
with `ind_sample` replaced by just `sample`. Support for mutable distributions
has been dropped; although it appears there may be a few genuine uses, these
are not used widely enough to justify the existance of two independent traits
or of having to provide mutable access to a distribution object. Both `Sample`
and `IndependentSample` are still available, but deprecated; they will be
removed in a future release.

`Distribution::sample` (as well as several other functions) can now be called
directly on type-erased (unsized) RNGs.

`RandSample` has been removed (see `Rand` deprecation and new `Standard`
distribution).

The `Closed01` wrapper has been removed, but `OpenClosed01` has been added.

#### Uniform distributions

Two new distributions are available:

-   `Standard` produces uniformly-distributed samples for many different types,
    and acts as a replacement for `Rand`
-   `Alphanumeric` samples `char`s from the ranges `a-z A-Z 0-9`

##### Ranges

The `Range` distribution has been heavily adapted, and renamed to `Uniform`:

-   `Uniform::new(low, high)` remains (half open `[low, high)`)
-   `Uniform::new_inclusive(low, high)` has been added, including `high` in the sample range
-   `Uniform::sample_single(low, high, rng)` is a faster variant for single usage sampling from `[low, high)`

`Uniform` can now be implemented for user-defined types; see the `uniform` module.

#### Non-uniform distributions

Two distributions have been added:

-   Poisson, modelling the number of events expected from a constant-rate
    source within a fixed time interval (e.g. nuclear decay)
-   Binomial, modelling the outcome of a fixed number of yes-no trials

The sampling methods are based on those in "Numerical Recipes in C".

##### Exponential and Normal distributions

The main `Exp` and `Normal` distributions are unchanged, however the
"standard" versions, `Exp1` and `StandardNormal` are no longer wrapper types,
but full distributions. Instead of writing `let Exp1(x) = rng.gen();` you now
write `let x = rng.sample(Exp1);`.
