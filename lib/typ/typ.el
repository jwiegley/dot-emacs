;;; typ.el --- type inference framework for Emacs Lisp compilers -*- lexical-binding: t -*-

;; Author: Iskander Sharipov <quasilyte@gmail.com>
;; Keywords: lisp

;;; Commentary:

;; "typ.el" defines two types of functions:
;; (a) functions that record type information and
;; (b) functions that answer type information queries.
;;
;; In conjunction, this may help us to achieve:
;; - Improved documentation (type hints in signatures)
;; - Better Emacs Lisp optimization
;; - Type checks from linters
;;
;; To get detailed documentation, visit:
;; https://github.com/Quasilyte/typ.el

;;; Code:

;; This is temporary measure for code decomposition.
;; Later it will be distributed as a proper multi-file package.
(load-file "./src/typ-private.el")
(load-file "./src/typ-public.el")
(load-file "./src/typ-default-annotations.el")

(provide 'typ)

;;; typ.el ends here
