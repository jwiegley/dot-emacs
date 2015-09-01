#! /bin/bash

LOCAL="$1"
REMOTE="$2"

rootdir="$(dirname "$BASH_SOURCE")"

if [ -d $LOCAL ]
then
    emacs --eval "(progn (setq debug-on-error t) (load-file \"$rootdir/dircmp.el\") (compare-directories \"$LOCAL\" \"$REMOTE\"))"
else
    emacs --eval "(ediff-files \"$LOCAL\" \"$REMOTE\")"
fi
