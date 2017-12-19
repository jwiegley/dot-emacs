#!/bin/bash

set -o errexit
set -o nounset

# Don't run tests tagged with @known-failure
cask exec ecukes --tags ~@known-failure "$@"
