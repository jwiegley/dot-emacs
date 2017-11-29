#!/bin/bash

if [ README.md -ot writeroom-mode.info ] ; then
    exit 0 # everything's fine
fi

# otherwise generate info file and git-add it.

git stash -q --keep-index

pandoc --read=markdown \
       --write=texinfo \
       --output=/home/joost/src/writeroom-mode/writeroom-mode.texi \
       --include-before-body=/home/joost/src/writeroom-mode/texi-before-body \
       --standalone \
       ./README.md

RESULT=$?

[ $RESULT == 0 ] && makeinfo ./writeroom-mode.texi && git add ./writeroom-mode.info

git stash pop -q

[ $RESULT -ne 0 ] && exit 1

exit 0
