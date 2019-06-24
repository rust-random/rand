# Derived from https://github.com/japaric/trust

set -ex

main() {
    cross test --target $TARGET --tests --no-default-features
  # TODO: add simd_support feature:
    cross test --target $TARGET --features=log
    cross test --target $TARGET --examples
    cross test --target $TARGET --manifest-path rand_core/Cargo.toml
    cross test --target $TARGET --manifest-path rand_core/Cargo.toml --features=serde1
    cross test --target $TARGET --manifest-path rand_core/Cargo.toml --no-default-features
    cross test --target $TARGET --manifest-path rand_distr/Cargo.toml
    cross test --target $TARGET --manifest-path rand_isaac/Cargo.toml --features=serde1
    cross test --target $TARGET --manifest-path rand_pcg/Cargo.toml --features=serde1
    cross test --target $TARGET --manifest-path rand_xorshift/Cargo.toml --features=serde1
    cross test --target $TARGET --manifest-path rand_xoshiro/Cargo.toml --features=serde1
    cross test --target $TARGET --manifest-path rand_chacha/Cargo.toml
    cross test --target $TARGET --manifest-path rand_hc/Cargo.toml
    cross test --target $TARGET --manifest-path rand_os/Cargo.toml
    cross test --target $TARGET --manifest-path rand_jitter/Cargo.toml
}

# we don't run the "test phase" when doing deploys
if [ -z $TRAVIS_TAG ]; then
    main
fi
