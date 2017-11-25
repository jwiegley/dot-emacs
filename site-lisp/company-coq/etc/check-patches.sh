#!/usr/bin/env bash
for dir in /build/coq*/; do
    coqtop=${dir}dist/bin/coqtop
    if [ -f "$coqtop" ]; then
       echo "Testing ${coqtop}:"
       $coqtop >/dev/null 2>&1 <<< 'Set Search Output Name Only. Redirect "/tmp/coqtest" SearchAbout nat max.'
       cat /tmp/coqtest.out
    fi
done
