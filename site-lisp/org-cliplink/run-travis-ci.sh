#!/usr/bin/env bash

function finish {
    echo "Killing testing server..."
    kill "$!"
}

trap finish EXIT

echo "Starting testing server..."
./run-testing-server.py &
sleep 1

emacs --batch --no-site-file --no-splash -l ert --script url-el-integration-tests.el || exit 1
emacs --batch --no-site-file --no-splash -l ert --script curl-integration-tests.el || exit 1
cask exec ert-runner || exit 1
