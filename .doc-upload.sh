pip install 'travis-cargo<0.2' --user && export PATH=$HOME/.local/bin:$PATH
travis-cargo --only nightly doc-upload
# Travis cares about exit status. travis-cargo apparently has non-zero exit status when already
# up to date, so we must ignore that.
true
