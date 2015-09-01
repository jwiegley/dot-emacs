#!/bin/sh

#cabal clean && cabal configure --enable-tests --enable-library-coverage --enable-library-profiling --enable-executable-profiling && cabal build && cabal test && cabal haddock
cabal clean && cabal configure --enable-tests && cabal build && cabal test && cabal haddock


