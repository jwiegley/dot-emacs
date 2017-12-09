#!/usr/bin/env bash

if [ -z "$EMACS" ] ; then
    EMACS="emacs"
fi

if [[ -n "$1" ]] ; then
    $EMACS -batch -l tests.el -l "$1" -f ert-run-tests-batch-and-exit || rc=$?
else
    for n in *-tests.el; do
        $EMACS -batch -l tests.el -l "$n" -f ert-run-tests-batch-and-exit || exit 1;
    done;
fi
exit $rc
