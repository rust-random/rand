# Security Policy

## Disclaimer

Rand is a community project and cannot provide legally-binding guarantees of
security.

## Security premises

### Marker traits

Rand provides the marker traits `CryptoRng`, `TryCryptoRng` and
`CryptoBlockRng`. Generators implementing one of these traits and used in a way
which meets the following additional constraints:

-   Instances of seedable RNGs (those implementing `SeedableRng`) are
    constructed with cryptographically secure seed values
-   The state (memory) of the RNG and its seed value are not exposed

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

`ThreadRng` will periodically reseed itself, thus placing an upper bound on the
number of bits of output from an instance before any advantage an attacker may
have gained through state-compromising side-channel attacks is lost.

[getrandom]: https://crates.io/crates/getrandom

### Distributions

Additionally, derivations from such an RNG (including the `Rng` trait,
implementations of the `Distribution` trait, and `seq` algorithms) should not
introduce significant bias other than that expected from the operation in
question (e.g. bias from a weighted distribution).

## Supported Versions

We will attempt to uphold these premises in the following crate versions,
provided that only the latest patch version is used, and with potential
exceptions for theoretical issues without a known exploit:

| Crate | Versions | Exceptions |
| ----- | -------- | ---------- |
| `rand` | 0.8 |  |
| `rand` | 0.7 |  |
| `rand` | 0.5, 0.6 | Jitter |
| `rand` | 0.4 | Jitter, ISAAC |
| `rand_core` | 0.2 - 0.6 | |
| `rand_chacha` | 0.1 - 0.3 | |

Explanation of exceptions:

-   Jitter: `JitterRng` is used as an entropy source when the primary source
    fails; this source may not be secure against side-channel attacks, see #699.
-   ISAAC: the [ISAAC](https://burtleburtle.net/bob/rand/isaacafa.html) RNG used
    to implement `ThreadRng` is difficult to analyse and thus cannot provide
    strong assertions of security.

## Known issues

In `rand` version 0.3 (0.3.18 and later), if `OsRng` fails, `ThreadRng` is
seeded from the system time in an insecure manner.

## Reporting a Vulnerability

To report a vulnerability, [open a new issue](https://github.com/rust-random/rand/issues/new).
Once the issue is resolved, the vulnerability should be [reported to RustSec](https://github.com/RustSec/advisory-db/blob/master/CONTRIBUTING.md).
