#!/bin/sh

# Run the command in a docker file.

# Assumes the two scripts in the docker directory have been run to
# create the GHC 7.6.3 and GHC 7.4.2 environments

#docker run -i -t alanz/haskell-platform-2012.4.0.0-64 /bin/bash


docker run -i -v $(pwd):/opt/haskell:rw -t alanz/HaRe-7.6.3-64   /bin/bash

# cd /opt/haskell
# cabal update
# cabal install --only-dependencies
# ./buildall.sh


