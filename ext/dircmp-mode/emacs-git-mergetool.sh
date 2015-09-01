#! /bin/bash

LOCAL="$1"
REMOTE="$2"
BASE="$3"
MERGED="$4"

if [ -f "$BASE" ]
then
    emacs --eval "(ediff-merge-files-with-ancestor \"$LOCAL\" \"$REMOTE\" \"$BASE\" nil \"$MERGED\")"
else
    emacs --eval "(ediff-merge-files \"$LOCAL\" \"$REMOTE\" nil \"$MERGED\")"
fi
