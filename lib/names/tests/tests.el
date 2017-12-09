(unless (fboundp 'function-put)
  (defalias 'function-put
    ;; We don't want people to just use `put' because we can't conveniently
    ;; hook into `put' to remap old properties to new ones.  But for now, there's
    ;; no such remapping, so we just call `put'.
    #'(lambda (f prop value) (put f prop value))
    "Set function F's property PROP to VALUE.
The namespace for PROP is shared with symbols.
So far, F can only be a symbol, not a lambda expression."))

(progn
  (add-to-list 'load-path (expand-file-name "../"))
  (add-to-list 'load-path (expand-file-name "./"))
  (byte-compile-file (expand-file-name "../names.el"))
  (require 'ert)
  (fset 'ert--print-backtrace 'ignore)
;; (require 'names)
  ;; (setq debug-on-error t)
  ;; (setq byte-compile-debug t)
  )
