#!/usr/bin/env bash
find /build/coq-8.5/theories/ -name *.v | xargs ag --color --line-number --column --stats -- "[a-zA-Z_][0-9]+\\b"
