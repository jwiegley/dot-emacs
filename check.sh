#!/bin/sh

set -eu

: ${EMACS:=emacs}

exec ${EMACS} --batch --eval '(progn
  (byte-compile-file "paredit.el" t)
  (byte-compile-file "test.el" t)
)'
