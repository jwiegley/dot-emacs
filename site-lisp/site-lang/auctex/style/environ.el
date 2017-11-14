;;; environ.el --- AUCTeX style for `environ.sty' version v0.3

;; Copyright (C) 2015, 2016 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2015-07-04
;; Keywords: tex

;; This file is part of AUCTeX.

;; AUCTeX is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; AUCTeX is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with AUCTeX; see the file COPYING.  If not, write to the Free
;; Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
;; 02110-1301, USA.

;;; Commentary:

;; This file adds support for `environ.sty' version v0.3 from
;; 2014/05/04.  `environ.sty' is part of TeXLive.

;; Name of new env's defined with `\NewEnviron' are automatically
;; added to list of known env's, e.g.:
;;
;;     \NewEnviron{test}{<macro code>}
;;
;; `test' will be in completion list upon `C-c C-e'.

;; More sophisticated definions must go through AUCTeX's parser, e.g.:
;;
;;     \NewEnviron{test}[2][]{<macro code>}
;;
;; After a definition like this, you have to invoke `C-c C-n' to get
;; the correct completion.

;;; Code:

(defvar LaTeX-auto-environ-NewEnviron nil
  "Temporary for parsing the arguments of `\\NewEnviron'
from `environ' package.")

(defvar LaTeX-environ-NewEnviron-regexp
  `(,(concat "\\\\\\(?:Ren\\|N\\)ewEnviron"
	     "[ \t\n\r]*{\\([A-Za-z0-9]+\\)}%?"
	     "[ \t\n\r]*\\[?\\([0-9]?\\)\\]?%?"
	     "[ \t\n\r]*\\(\\[\\)?")
    (1 2 3) LaTeX-auto-environ-NewEnviron)
  "Matches the argument of `\\NewEnviron' and `\\RenewEnviron'
from `environ.sty'.")

(defun LaTeX-environ-auto-prepare ()
  "Clear temporary variable from `environ.sty' before parsing."
  (setq LaTeX-auto-environ-NewEnviron nil))

(defun LaTeX-environ-auto-cleanup ()
  "Process the parsed results of `\\NewEnviron'."
  (dolist (env-args LaTeX-auto-environ-NewEnviron)
    (let ((env  (car   env-args))
	  (args (cadr  env-args))
	  (opt  (nth 2 env-args)))
      (cond (;; opt. 1st argument and mandatory argument(s)
	     (and args (not (string-equal args ""))
		  opt  (not (string-equal opt  "")))
	     (add-to-list 'LaTeX-auto-environment
			  (list env 'LaTeX-env-args (vector "argument")
				(1- (string-to-number args)))))
	    (;; mandatory argument(s) only
	     (and args (not (string-equal args ""))
		  (string-equal opt ""))
	     (add-to-list 'LaTeX-auto-environment
			  (list env (string-to-number args))))
	    (t ; No args
	     (add-to-list 'LaTeX-auto-environment (list env)))))))

(add-hook 'TeX-auto-prepare-hook #'LaTeX-environ-auto-prepare t)
(add-hook 'TeX-auto-cleanup-hook #'LaTeX-environ-auto-cleanup t)
(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)

(defun TeX-arg-environ-final-code (_optional)
  "Query for the presence of optional `final code' as argument to
`\\NewEnviron' and insert the appropriate brackets."
  (let ((fincode (y-or-n-p "With optional final code? ")))
    (when fincode
	(insert "[]"))))

(TeX-add-style-hook
 "environ"
 (lambda ()

   ;; Add it to the parser
   (TeX-auto-add-regexp LaTeX-environ-NewEnviron-regexp)

   (TeX-add-symbols

    ;; \NewEnviron{<name>}[<No.args>][<Opt.arg.>]{<Macro code>}[<Final code>]
    '("NewEnviron"
      (TeX-arg-define-environment "Environment")
      [ "Number of arguments" ] [ "argument" ] t TeX-arg-environ-final-code)

    '("RenewEnviron"
      (TeX-arg-environment "Environment")
      [ "Number of arguments" ] [ "argument" ] t TeX-arg-environ-final-code)

    ;; Insert a pair of braces and we're done
    '("environfinalcode" t)

    ;; Pre-defined
    '("BODY")

    ;; Define another macro instead of \BODY
    '("environbodyname" TeX-arg-define-macro))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("NewEnviron"      "{[[{[")
				("RenewEnviron"    "{[[{[")
				("environbodyname" "|{\\"))
			      'function)))
  LaTeX-dialect)

(defvar LaTeX-environ-package-options nil
  "Package options for the environ package.")

;;; environ.el ends here
