#!/bin/sh

set -Ceu

: ${EMACS:=emacs}

exec ${EMACS} --batch --load paredit.el --eval '
(with-temp-buffer
  (paredit-insert-html-examples)
  (write-file "paredit.html"))
'
