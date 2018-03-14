# Derived from https://github.com/japaric/trust

set -ex

main() {
    if [ ! -z $DISABLE_TESTS ]; then
        cross build --all --no-default-features --target $TARGET --release
        if [ -z $DISABLE_STD ]; then
            cross build --features log,serde-1 --target $TARGET
        fi
        return
    fi

    if [ ! -z $NIGHTLY ]; then
        cross test --all --tests --no-default-features --features alloc --target $TARGET
        cross test --features serde-1,log,nightly --target $TARGET
        cross test --all --benches --target $TARGET
    else
        cross test --all --tests --no-default-features --target $TARGET
        cross test --features serde-1,log --target $TARGET
    fi
}

# we don't run the "test phase" when doing deploys
if [ -z $TRAVIS_TAG ]; then
    main
fi
