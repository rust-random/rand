pip install 'travis-cargo<0.2' --user && export PATH=$HOME/.local/bin:$PATH
travis-cargo --only nightly doc-upload
