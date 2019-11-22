set -ex

MIRI_NIGHTLY=nightly-$(curl -s https://rust-lang.github.io/rustup-components-history/x86_64-unknown-linux-gnu/miri)
echo "Installing latest nightly with Miri: $MIRI_NIGHTLY"
rustup default "$MIRI_NIGHTLY"

rustup component add miri
cargo miri setup

cargo miri test --no-default-features
cargo miri test --features=log
cargo miri test --manifest-path rand_core/Cargo.toml
cargo miri test --manifest-path rand_core/Cargo.toml --features=serde1
cargo miri test --manifest-path rand_core/Cargo.toml --no-default-features
#cargo miri test --manifest-path rand_distr/Cargo.toml # no unsafe and lots of slow tests
cargo miri test --manifest-path rand_pcg/Cargo.toml --features=serde1
cargo miri test --manifest-path rand_chacha/Cargo.toml --no-default-features
cargo miri test --manifest-path rand_hc/Cargo.toml
