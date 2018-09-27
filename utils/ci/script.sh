# Derived from https://github.com/japaric/trust

set -ex

main() {
    if [ ! -z $DISABLE_TESTS ]; then    # tests are disabled
        cross build --no-default-features --target $TARGET --release
        if [ -z $DISABLE_STD ]; then    # std is enabled
            cross build --features log,serde1 --target $TARGET
        fi
        return
    fi

    if [ ! -z $NIGHTLY ]; then  # have nightly Rust
        cross test --lib --no-default-features --features alloc --target $TARGET
        cross test --all-features --target $TARGET
        cross test --benches --features=nightly --target $TARGET
        cross test --examples --target $TARGET
        cross test --package rand_core --target $TARGET
        cross test --package rand_core --no-default-features --features=alloc --target $TARGET
        cross test --package rand_isaac --features=serde1 --target $TARGET
        cross test --package rand_chacha --target $TARGET
        cross test --package rand_hc128 --target $TARGET
        cross test --package rand_xorshift --features=serde1 --target $TARGET
    else    # have stable Rust
        cross test --lib --no-default-features --target $TARGET
        cross test --features=serde1,log --target $TARGET
        cross test --examples --target $TARGET
        cross test --package rand_core --target $TARGET
        cross test --package rand_core --no-default-features --target $TARGET
        cross test --package rand_isaac --features=serde1 --target $TARGET
        cross test --package rand_chacha --target $TARGET
        # cross test --package rand_hc128 ---target $TARGET  # fails for unknown reasons
        cross test --package rand_xorshift --features=serde1 --target $TARGET
    fi
}

# we don't run the "test phase" when doing deploys
if [ -z $TRAVIS_TAG ]; then
    main
fi
