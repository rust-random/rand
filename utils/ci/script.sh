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
        cross test --tests --no-default-features --features alloc --target $TARGET
        cross test --package rand_core --no-default-features --features alloc --target $TARGET
        cross test --features serde1,log,nightly,alloc --target $TARGET
        cross test --all --benches --target $TARGET
    else    # have stable Rust
        cross test --tests --no-default-features --target $TARGET
        cross test --package rand_core --no-default-features --target $TARGET
        cross test --features serde1,log --target $TARGET
    fi
}

# we don't run the "test phase" when doing deploys
if [ -z $TRAVIS_TAG ]; then
    main
fi
