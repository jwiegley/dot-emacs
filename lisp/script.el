#!/usr/local/bin/emacs --script

;; This is actually a difficult example to emulate in Bash, since neither head
;; nor tail has the concept of "all by the last X lines".

(load "~/.emacs.d/load-path" nil t)

(require 'deferred)

(deferred:sync!
  (deferred:$
    (deferred:parallel
      (lambda ()
        (deferred:process "ls" "-la"))
      (lambda ()
        (deferred:process "ls" "-lha")))

    (deferred:nextc it
      (lambda (texts)
        (apply #'append (mapcar #'(lambda (text)
                                    (split-string text "\n" t))
                                texts))))

    (deferred:nextc it
      (lambda (lines)
        (nbutlast lines 15)))

    (deferred:nextc it
      (lambda (lines)
        (mapcar #'message lines)))))
