# Derived from https://github.com/japaric/trust

set -ex

# ----- Options -----

# TARGET enables cross-building
if [ -z $TARGET ]; then
    CARGO=cargo
elif [ "$TARGET" = "i686-unknown-linux-musl" ]; then
    CARGO=cargo
    TARGET="--target $TARGET"
else
    CARGO=cross
    TARGET="--target $TARGET"
fi

# ALLOC defaults on; is disabled for rustc < 1.36
if [ -z $ALLOC ]; then
    ALLOC=1
fi

# NIGHTLY defaults off


# ----- Script -----

main() {
  if [ "0$NIGHTLY" -ge 1 ]; then
    $CARGO test $TARGET --all-features
    $CARGO test $TARGET --benches --features=nightly
    $CARGO test $TARGET --manifest-path rand_distr/Cargo.toml --benches
  else
    # all stable features:
    $CARGO test $TARGET --features=serde1,log,small_rng
  fi

  if [ "$ALLOC" -ge 1 ]; then
    $CARGO test $TARGET --tests --no-default-features --features=alloc,getrandom,small_rng
    $CARGO test $TARGET --manifest-path rand_core/Cargo.toml --no-default-features --features=alloc
  fi
  
  $CARGO test $TARGET --tests --no-default-features
  $CARGO test $TARGET --examples
  
  $CARGO test $TARGET --manifest-path rand_core/Cargo.toml
  $CARGO test $TARGET --manifest-path rand_core/Cargo.toml --no-default-features
  $CARGO test $TARGET --manifest-path rand_core/Cargo.toml --no-default-features --features=getrandom
  
  $CARGO test $TARGET --manifest-path rand_distr/Cargo.toml
  $CARGO test $TARGET --manifest-path rand_pcg/Cargo.toml --features=serde1
  $CARGO test $TARGET --manifest-path rand_chacha/Cargo.toml
  $CARGO test $TARGET --manifest-path rand_hc/Cargo.toml
}

# we don't run the "test phase" when doing deploys
if [ -z $TRAVIS_TAG ]; then
    main
fi
