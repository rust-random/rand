# Security Policy

## Disclaimer

Rand is a community project and cannot provide legally-binding guarantees of
security.

## Security premises

### Marker traits

Rand provides the marker traits `CryptoRng`, `TryCryptoRng` and
`CryptoBlockRng`. Generators (RNGs) implementing one of these traits which are
used according to these additional constraints:

-   The generator may be constructed using `std::default::Default` where the
    generator supports this trait. Note that generators should *only* support
    `Default` where the `default()` instance is appropriately seeded: for
    example `OsRng` has no state and thus has a trivial `default()` instance
    while `ThreadRng::default()` returns a handle to a thread-local instance
    seeded using `OsRng`.
-   The generator may be constructed using `rand_core::SeedableRng` in any of
    the following ways where the generator supports this trait:

    -   Via `SeedableRng::from_seed` using a cryptographically secure seed value
    -   Via `SeedableRng::from_rng` or `try_from_rng` using a cryptographically
        secure source `rng`
    -   Via `SeedableRng::from_os_rng` or `try_from_os_rng`
-   The state (memory) of the generator and its seed value (or source `rng`) are
    not exposed

are expected to provide the following:

-   An attacker cannot predict the output with more accuracy than what would be
    expected through pure chance since each possible output value of any method
    under the above traits which generates output bytes (including
    `RngCore::next_u32`, `RngCore::next_u64`, `RngCore::fill_bytes`,
    `TryRngCore::try_next_u32`, `TryRngCore::try_next_u64`,
    `TryRngCore::try_fill_bytes` and `BlockRngCore::generate`) should be equally
    likely
-   Knowledge of prior outputs from the generator does not aid an attacker in
    predicting future outputs

### Specific generators

`OsRng` is a stateless "generator" implemented via [getrandom]. As such, it has
no possible state to leak and cannot be improperly seeded.

`StdRng` is a `CryptoRng` and `SeedableRng` using a pseudo-random algorithm
selected for good security and performance qualities. Since it does not offer
reproducibility of output, its algorithm may be changed in any release version.

`ChaCha12Rng` and `ChaCha20Rng` are selected pseudo-random generators
distributed by the `rand` project which meet the requirements of the `CryptoRng`
trait and implement `SeedableRng` with a commitment to reproducibility of
results.

`ThreadRng` is a conveniently-packaged generator over `StdRng` offering
automatic seeding from `OsRng`, periodic reseeding and thread locality.
This random source is intended to offer a good compromise between cryptographic
security, fast generation with reasonably low memory and initialization cost
overheads, and robustness against misuse.

[getrandom]: https://crates.io/crates/getrandom

### Distributions

Methods of the `Rng` trait, functionality of the `rand::seq` module and
implementators of the `Distribution` trait are expected, while using a
cryptographically secure `CryptoRng` instance meeting the above constraints,
to not introduce significant bias to their operation beyond what would be
expected of the operation. Note that the usage of 'significant' here permits
some bias, as noted for example in the documentation of the `Uniform`
distribution.

## Supported Versions

We aim to provide security fixes in the form of a new patch version for the
latest release version of `rand` and its dependencies `rand_core` and
`chacha20`, as well as for prior major and minor releases which were, at some
time during the previous 12 months, the latest release version.

## Reporting a Vulnerability

If you have discovered a security vulnerability in this project, please report it privately. **Do not disclose it as a public issue.** This gives us time to work with you to fix the issue before public exposure, reducing the chance that the exploit will be used before a patch is released.

Please disclose it at [security advisory](https://github.com/rust-random/rand/security/advisories/new).

This project is maintained by a team of volunteers on a reasonable-effort basis. As such, please give us at least 90 days to work on a fix before public exposure.
