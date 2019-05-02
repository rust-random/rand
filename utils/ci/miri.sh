set -ex

if rustup component add miri && cargo miri setup ; then
    cargo miri test --no-default-features -- -Zmiri-seed=42 -- -Zunstable-options --exclude-should-panic
    cargo miri test --features=serde1,log -- -Zmiri-seed=42 -- -Zunstable-options --exclude-should-panic
    cargo miri test --manifest-path rand_core/Cargo.toml
    cargo miri test --manifest-path rand_core/Cargo.toml --no-default-features
    #cargo miri test --manifest-path rand_distr/Cargo.toml # no unsafe and lots of slow tests
    cargo miri test --manifest-path rand_isaac/Cargo.toml --features=serde1
    cargo miri test --manifest-path rand_pcg/Cargo.toml --features=serde1
    cargo miri test --manifest-path rand_xorshift/Cargo.toml --features=serde1
    cargo miri test --manifest-path rand_xoshiro/Cargo.toml
    cargo miri test --manifest-path rand_chacha/Cargo.toml
    cargo miri test --manifest-path rand_hc/Cargo.toml
    cargo miri test --manifest-path rand_jitter/Cargo.toml
    cargo miri test --manifest-path rand_os/Cargo.toml -- -Zmiri-seed=42
fi
