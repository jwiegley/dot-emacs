;;; tramp2-compat.el --- TRAMP2 Emacs/XEmacs compatibility routines.

;; Copyright (C) 2001 by Daniel Pittman <daniel@localhost>

;;; Commentary:

;; This module contains code that allows XEmacs and Emacs to inter-operate
;; politely. This is somewhat essential as it makes life easier for all of us.

;; Why can't we all just get along?

;;; Code:

;; NOTE: *DON'T* require tramp2 here, even if we are byte-compiling.
;; This will cause an infloop of dependencies...

;; XEmacs provides `define-error' to make structured error handling easier for
;; the average mortal. Emacs 20.7.2 doesn't. This makes it easier for all of
;; us. :)
(unless (fboundp 'define-error)
  
(defun define-error (error-sym doc-string &optional inherits-from)
  "Define a new error, denoted by ERROR-SYM.
DOC-STRING is an informative message explaining the error, and will be
printed out when an unhandled error occurs.
ERROR-SYM is a sub-error of INHERITS-FROM (which defaults to `error').

\[`define-error' internally works by putting on ERROR-SYM an `error-message'
property whose value is DOC-STRING, and an `error-conditions' property
that is a list of ERROR-SYM followed by each of its super-errors, up
to and including `error'.  You will sometimes see code that sets this up
directly rather than calling `define-error', but you should *not* do this
yourself.]"
  (unless (symbolp error-sym)  (error 'wrong-type-argument (list 'symbolp error-sym)))
  (unless (stringp doc-string) (error 'wrong-type-argument (list 'stringp doc-string)))

  (put error-sym 'error-message doc-string)
  (or inherits-from (setq inherits-from 'error))
  (let ((conds (get inherits-from 'error-conditions)))
    (or conds (signal 'error (list "Not an error symbol" error-sym)))
    (put error-sym 'error-conditions (cons error-sym conds))))

)


;; A more useful error reporting tool. This works with both XEmacs and Emacs.
(defun tramp2-error (&rest args)
  (signal 'tramp2-file-error args))


;; Finding the point at the start and end of the line.
(cond
 ((fboundp 'point-at-eol)	(defalias 'tramp2-point-at-eol #'point-at-eol))
 ((fboundp 'line-end-position)	(defalias 'tramp2-point-at-eol #'line-end-position))
 (t (defalias 'tramp2-point-at-eol #'(lambda () (save-excursion (end-of-line) (point))))))

(cond
 ((fboundp 'point-at-bol)	(defalias 'tramp2-point-at-bol #'point-at-bol))
 ((fboundp 'line-beginning-position)	(defalias 'tramp2-point-at-bol #'line-beginning-position))
 (t (defalias 'tramp2-point-at-bol #'(lambda () (save-excursion (beginning-of-line) (point))))))



;; Work around the Emacs `accept-process-output' function which does not
;; support floating point wait times.
(if (catch 'done
      (condition-case nil
	  (accept-process-output nil 0.1)
	(error (throw 'done t))
	nil))
    ;; Wrap the accept-process-input call...
    (defsubst tramp2-accept-process-output (&optional process timeout-secs timeout-msecs)
      "Call accept-process-output with only integer values for timeout."
      (accept-process-output process timeout-secs
			     (floor (* 1000 (- timeout-secs (floor timeout-secs))))))
  (defalias 'tramp2-accept-process-output #'accept-process-output))
   

(provide 'tramp2-compat)

;;; tramp2-compat.el ends here
