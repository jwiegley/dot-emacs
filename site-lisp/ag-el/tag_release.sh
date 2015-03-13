#!/bin/bash

if [[ "$#" -ne 1 ]]; then
    echo "You need to specify a tag version"
    echo "$ ./tag_release.sh 0.3"
    exit 1
fi

git tag -a "$@"
git push --tags
