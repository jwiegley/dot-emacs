#!/bin/bash

set -ex

cask eval "(progn (require 'elisp-refs-bench) (elisp-refs-bench))"
