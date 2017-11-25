#!/usr/bin/env bash

if [ $# -ne 2 ]; then
    cat <<EOF
Use: $0 <VERSION>"
- VERSION    version to release (0.1.6 for example)
- PACKAGE    package to release

To install the token, execute the install-marmalade-token.sh.
EOF
    exit 1;
fi
VERSION=$1
PACKAGE=$2

WDIR=$(dirname $0)

# launched from the current dev branch

git fetch -p --all

git checkout master

git merge upstream/master

git tag -a -s $VERSION

git push upstream --tag

make package

./upload-to-marmalade.sh $VERSION $PACKAGE
