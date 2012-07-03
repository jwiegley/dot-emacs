#!/usr/local/bin/emacs --script

;; This is actually a difficult example to emulate in Bash, since neither head
;; nor tail has the concept of "all by the last X lines".

(load "~/.emacs.d/load-path" nil t)

(require 'deferred)

(deferred:sync!
  (deferred:$
    (apply #'deferred:process command-line-args-left)

    (deferred:nextc it
      (lambda (text)
        (split-string text "\n" t)))

    (deferred:nextc it
      (lambda (lines)
        (nbutlast lines 15)))

    (deferred:nextc it
      (lambda (lines)
        (mapcar #'(lambda (line) (princ line) (terpri)) lines)))))
