# This script takes care of testing your crate

set -ex

# TODO This is the "test phase", tweak it as you see fit
main() {
    cross build --target $TARGET
    cross build --all --no-default-features --target $TARGET --release
    if [ ! -z $NIGHTLY ]; then
        cross doc --no-deps --features nightly
    fi

    if [ ! -z $DISABLE_TESTS ]; then
        return
    fi

    cross test --all --target $TARGET

    if [ ! -z $NIGHTLY ]; then
        cross test --all --features nightly --target $TARGET
        cross test --all --benches --target $TARGET
    fi
}

# we don't run the "test phase" when doing deploys
if [ -z $TRAVIS_TAG ]; then
    main
fi
