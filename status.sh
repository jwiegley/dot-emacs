#!/bin/sh

for i in $(git remote); do
    if [[ $i =~ ^ext\/(.*) ]]; then
        proj=${BASH_REMATCH[1]}
        if [[ ! -d lib/$proj &&
              ! -d lisp/$proj &&
              ! -d site-lisp/$proj &&
              ! -d override/$proj ]]; then
            echo "not checked out:" $proj
        else
            for d in lisp lib site-lisp override; do
                if [[ -d $d/$proj && -f $d/$proj/.git/config ]]; then
                    echo $d/$proj is now cloned
                fi
            done
        fi
    fi
done
