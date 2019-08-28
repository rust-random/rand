# Derived from https://github.com/japaric/trust

set -ex

# ----- Options -----

# TARGET enables cross-building
if [ -z $TARGET ]; then
    CARGO=cargo
else
    CARGO="cross --target $TARGET"
fi

# ALLOC defaults on; is disabled for rustc < 1.36
if [ -z $ALLOC ]; then
    ALLOC=1
fi

# NIGHTLY defaults off


# ----- Script -----

main() {
  if [ "0$NIGHTLY" -ge 1 ]; then
    $CARGO test --all-features
    $CARGO test --benches --features=nightly
  else
    # all stable features:
    $CARGO test --features=serde1,log,small_rng
  fi

  if [ "$ALLOC" -ge 1 ]; then
    $CARGO test --tests --no-default-features --features=alloc,getrandom,small_rng
  fi
  
  $CARGO test --tests --no-default-features
  $CARGO test --examples
  
  $CARGO test --manifest-path rand_core/Cargo.toml
  $CARGO test --manifest-path rand_core/Cargo.toml --no-default-features
  $CARGO test --manifest-path rand_core/Cargo.toml --no-default-features --features=alloc
  $CARGO test --manifest-path rand_core/Cargo.toml --no-default-features --features=getrandom
  
  $CARGO test --manifest-path rand_distr/Cargo.toml
  $CARGO test --manifest-path rand_isaac/Cargo.toml --features=serde1
  $CARGO test --manifest-path rand_pcg/Cargo.toml --features=serde1
  $CARGO test --manifest-path rand_xorshift/Cargo.toml --features=serde1
  $CARGO test --manifest-path rand_xoshiro/Cargo.toml
  $CARGO test --manifest-path rand_chacha/Cargo.toml
  $CARGO test --manifest-path rand_hc/Cargo.toml
  $CARGO test --manifest-path rand_jitter/Cargo.toml
  $CARGO test --manifest-path rand_os/Cargo.toml
}

# we don't run the "test phase" when doing deploys
if [ -z $TRAVIS_TAG ]; then
    main
fi
