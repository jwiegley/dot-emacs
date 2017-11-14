;;; newfloat.el --- AUCTeX style for `newfloat.sty' (v1.1-109)

;; Copyright (C) 2015 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2015-09-19
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

;; This file adds support for `newfloat.sty' (v1.1-109) from 2015/09/17.
;; `newfloat.sty' is part of TeXLive.

;; This style has some facilities to process the newly defined
;; floating environments within AUCTeX, e.g. indentation, label
;; addition etc.  Currently it makes provision for `figure', `table'
;; and `verbatim' floating types.  To make things work, the style
;; needs some help from the user.  When a new floating environment is
;; defined, the user should pass the floating type as a comment to
;; AUCTeX, e.g.
;;
;;     \DeclareFloatingEnvironment[
;;       name=Code,
;;       listname={List of Codes},
;;       fileext=lol]{code}  %  {verbatim}
;;
;; Note the `{verbatim}' as a comment after the name of the float env.
;; Due to parsing reasons, this key-word must be in the same line as
;; the name of the float and enclosed in braces `{}'.
;;
;; Before the opening brace, only spaces and comment chars `%' are
;; allowed.  Anything following the closing brace `}' is ignored.

;; If things do not work or when in doubt, press `C-c C-n'.  Comments
;; for improvement are welcome.

;;; Code:

;; Needed for auto-parsing.
(require 'tex)

(defvar LaTeX-newfloat-key-val-options
  '(("fileext")
    ("listname")
    ("name")
    ("placement" ("t" "b" "p" "tbp" "htbp"))
    ("chapterlistsgaps" ("on" "off")))
  "Key=value options for newfloat macros.")

(defvar LaTeX-newfloat-key-val-options-local nil
  "Buffer-local Key=value options for newfloat macros.")
(make-variable-buffer-local 'LaTeX-newfloat-key-val-options-local)

;; Setup parsing for \DeclareFloatingEnvironment:
(TeX-auto-add-type "newfloat-DeclareFloatingEnvironment" "LaTeX")

(defvar LaTeX-newfloat-DeclareFloatingEnvironment-regex
  `(,(concat "\\\\DeclareFloatingEnvironment"
	     "[ \t\n\r%]*"
	     "\\["
	     "[ \t\n\r%{}a-zA-Z0-9=,-]*"
	     "\\]"
	     "[ \t\n\r%]*"
	     "{\\([^}]+\\)}"
	     "\\(?:[ %]*{\\([^}]*\\)}\\)?")
    (1 2) LaTeX-auto-newfloat-DeclareFloatingEnvironment)
  "Matches the argument of `\\DeclareFloatingEnvironment' from
`newfloat.sty'.")

(defun LaTeX-newfloat-auto-prepare ()
  "Clear `LaTeX-auto-newfloat-DeclareFloatingEnvironment' before parsing."
  (setq LaTeX-auto-newfloat-DeclareFloatingEnvironment nil))

(defun LaTeX-newfloat-auto-cleanup ()
  "Process definded floats with \\DeclareFloatingEnvironment.
Depending on floating type passed as a comment to
AUCTeX (\"figure\", \"table\" or \"verbatim\"), update
`LaTeX-figure-label' and `LaTeX-table-label'.  If RefTeX is
loaded, add the new floating environment via
`reftex-add-label-environments'.  For \"verbatim\" environments,
update `LaTeX-indent-environment-list' to suppress indentation.
If `caption.el' is loaded, add the new floating environment to
`LaTeX-caption-supported-float-types'.  Also define the macros
\"listofENVs\" and \"listofENVes\"."
  (dolist (flt-type (LaTeX-newfloat-DeclareFloatingEnvironment-list))
    (let ((flt  (car  flt-type))
	  (type (cadr flt-type)))
      (cond ((string-equal type "figure")
	     (LaTeX-add-environments `(,flt LaTeX-env-figure))
	     (add-to-list 'LaTeX-label-alist `(,flt . LaTeX-figure-label) t)
	     (when (fboundp 'reftex-add-label-environments)
	       (reftex-add-label-environments
		`((,flt ?f ,LaTeX-figure-label "~\\ref{%s}" caption nil nil)))))
	    ((string-equal type "table")
	     (LaTeX-add-environments `(,flt LaTeX-env-figure))
	     (add-to-list 'LaTeX-label-alist `(,flt . LaTeX-table-label) t)
	     (when (fboundp 'reftex-add-label-environments)
	       (reftex-add-label-environments
		`((,flt ?t ,LaTeX-table-label "~\\ref{%s}" caption nil nil)))))
	    ((string-equal type "verbatim")
	     (LaTeX-add-environments `(,flt ["Float Position"]))
	     (add-to-list (make-local-variable 'LaTeX-indent-environment-list)
			  `(,flt current-indentation) t)
	     (add-to-list 'LaTeX-label-alist `(,flt . LaTeX-listing-label) t)
	     (when (fboundp 'reftex-add-label-environments)
	       (reftex-add-label-environments
		`((,flt ?l "lst:" "~\\ref{%s}" caption nil nil)))))
	    (t
	     (LaTeX-add-environments `(,flt ["Float Position"]))))
      (when (boundp 'LaTeX-caption-supported-float-types)
	(add-to-list (make-local-variable 'LaTeX-caption-supported-float-types)
		     flt))
      (if (string-equal "e" (substring flt -1))
	  (TeX-add-symbols (concat "listof" flt "s"))
	(TeX-add-symbols
	 (concat "listof" flt "s")
	 (concat "listof" flt "es"))))))

(add-hook 'TeX-auto-prepare-hook #'LaTeX-newfloat-auto-prepare t)
(add-hook 'TeX-auto-cleanup-hook #'LaTeX-newfloat-auto-cleanup t)
(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)

(TeX-add-style-hook
 "newfloat"
 (lambda ()

   ;; Add newfloat to the parser.
   (TeX-auto-add-regexp LaTeX-newfloat-DeclareFloatingEnvironment-regex)

   ;; Depending on class, add "within" key to the local options list
   ;; and use it.
   (setq LaTeX-newfloat-key-val-options-local
	 (copy-alist LaTeX-newfloat-key-val-options))

   (if (< (LaTeX-largest-level) 2)
       (add-to-list 'LaTeX-newfloat-key-val-options-local
		    '("within" ("chapter" "section" "none")))
     (add-to-list 'LaTeX-newfloat-key-val-options-local
		  '("within" ("section" "none"))))

   ;; Commands:
   (TeX-add-symbols
    '("DeclareFloatingEnvironment"
      [TeX-arg-key-val LaTeX-newfloat-key-val-options-local]
      (TeX-arg-eval
       (lambda ()
	 (let ((newfloat (TeX-read-string
			 (TeX-argument-prompt nil nil "Floating environment"))))
	   (LaTeX-add-newfloat-DeclareFloatingEnvironments newfloat)
	   (format "%s" newfloat)))))

    '("SetupFloatingEnvironment"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt nil nil "Floating environment")
		    (mapcar 'car (LaTeX-newfloat-DeclareFloatingEnvironment-list)))
      (TeX-arg-key-val LaTeX-newfloat-key-val-options-local))

    '("ForEachFloatingEnvironment" t)
    '("ForEachFloatingEnvironment*" t)

    '("PrepareListOf"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt nil nil "Floating environment")
		    (mapcar 'car (LaTeX-newfloat-DeclareFloatingEnvironment-list)))
      t)

    '("newfloatsetup"
      (TeX-arg-eval
       (lambda ()
	 (let ((keyvals (TeX-read-key-val
			 nil
			 (append '(("chapterlistsgap"))
				 (if (< (LaTeX-largest-level) 2)
				     '(("within" ("chapter" "section" "none")))
				   '(("within" ("section" "none"))))))))
	   (format "%s" keyvals))))))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("DeclareFloatingEnvironment"  "[{")
				("SetupFloatingEnvironment"    "{{")
				("ForEachFloatingEnvironment"  "*{")
				("PrepareListOf"               "{{")
				("newfloatsetup"               "{"))
			      'function)))
 LaTeX-dialect)

(defun LaTeX-newfloat-package-options ()
  "Prompt for package options for the newfloat package."
  (TeX-read-key-val
   t
   (append
    '(("chapterlistsgap"))
    (if (< (LaTeX-largest-level) 2)
	'(("within" ("chapter" "section" "none")))
      '(("within" ("section" "none")))))))

;;; newfloat.el ends here
