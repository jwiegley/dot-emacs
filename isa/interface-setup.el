;; interface-setup.el Interface wrapper for Isabelle Proof General
;;
;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.
;;
;; Author: Markus Wenzel <wenzelm@in.tum.de>
;;
;; $Id$
;;

;;;
;;; X-Symbol mode
;;;

(let ((xsymbol-home (getenv "XSYMBOL_HOME"))
      (xsymbol (getenv "PROOFGENERAL_XSYMBOL"))
      (enable-var
       (if (equal (getenv "PROOFGENERAL_ASSISTANTS") "isa")
           'isa-x-symbol-enable 'isar-x-symbol-enable)))
  ;; setup the x-symbol package, if not already present
  (if (and xsymbol-home
           (not (fboundp 'x-symbol-initialize))
           (not (get 'x-symbol 'x-symbol-initialized)))
      (progn
        (load (expand-file-name "lisp/x-symbol/auto-autoloads" xsymbol-home))
        (push (expand-file-name "lisp/x-symbol" xsymbol-home) load-path)
        (if (boundp 'data-directory-list)
            (push (expand-file-name "etc/" xsymbol-home) data-directory-list))
        (x-symbol-initialize)))
  ;; tell Proof General about -x option
  (if (and xsymbol (not (equal xsymbol "")))
      (customize-set-variable enable-var (equal xsymbol "true"))))
