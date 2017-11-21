#!/usr/bin/env bash

for version in $*; do
    EMACS_NAME=emacs-$version
    # forge the right path
    PATH=$(evm bin $EMACS_NAME):~/.evm/bin/:~/.cask/bin/:/usr/bin/:/bin
    # use the emacs version
    evm use $EMACS_NAME
    # check the right emacs version is found
    emacs --version
    # install deps
    cask install
    # run the tests
    make test
done
