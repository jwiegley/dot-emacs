;;; theorem.el --- AUCTeX style for `theorem.sty' (v2.2c)

;; Copyright (C) 2015 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2015-10-31
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

;; This file adds support for `theorem.sty' (v2.2c) from 2014/10/28.
;; `theorem.sty' is a standard LaTeX package and part of TeXLive.

;; The style provides the function `LaTeX-theorem-env-label' which
;; enables new defined environments with "\newtheoreom" to interact
;; with AUCTeX and RefTeX mechanisms for inserting labels.  Check
;; docstring of `LaTeX-theorem-env-label' for instructions.

;;; Code:

(defvar LaTeX-theorem-theoremstyle-list
  '(("plain") ("break") ("margin") ("change")
    ("marginbreak") ("changebreak"))
  "List of theorem styles provided by `theorem.sty'.")

(defvar LaTeX-theorem-fontdecl
  '(;; family
    "rmfamily" "sffamily" "ttfamily"
    ;; series
    "mdseries" "bfseries"
    ;; shape
    "upshape" "itshape" "slshape" "scshape"
    ;; size
    "tiny"  "scriptsize" "footnotesize"
    "small" "normalsize" "large"
    "Large" "LARGE" "huge" "Huge"
    ;; reset macro
    "normalfont")
  "List of font declaration commands for \"\\theorem(body\|header)font\".")

(defun LaTeX-arg-theorem-fontdecl (optional &optional prompt)
  "Prompt for font declaration commands in \"\\theorem(body\|header)font\".
If OPTIONAL is non-nil, insert the resulting value as an optional
argument.  Use PROMPT as the prompt string."
  ;; `INITIAL-INPUT' (5th argument to `TeX-completing-read-multiple')
  ;; is hard-coded to `TeX-esc'.
  (let* ((crm-separator (regexp-quote TeX-esc))
	 (fontdecl (mapconcat 'identity
			      (TeX-completing-read-multiple
			       (TeX-argument-prompt optional prompt "Font")
			       LaTeX-theorem-fontdecl nil nil TeX-esc)
			      TeX-esc)))
    (TeX-argument-insert fontdecl optional)))

(defun LaTeX-theorem-env-label (environment)
  "Insert ENVIRONMENT, query for an optional argument and prompt
for label.  AUCTeX users should add ENVIRONMENT to
`LaTeX-label-alist' via customize or in init-file with:

  (add-to-list \\='LaTeX-label-alist \\='(\"lemma\" . \"lem:\"))

RefTeX users should customize or add ENVIRONMENT to
`LaTeX-label-alist' and `reftex-label-alist', e.g.

  (add-to-list \\='LaTeX-label-alist \\='(\"lemma\" . \"lem:\"))
  (add-to-list \\='reftex-label-alist
	       \\='(\"lemma\" ?m \"lem:\" \"~\\ref{%s}\"
		 nil (\"Lemma\" \"lemma\") nil))"
  (let ((opthead (TeX-read-string
		  (TeX-argument-prompt t nil "Heading"))))
    (LaTeX-insert-environment environment
			      (when (and opthead
					 (not (string= opthead "")))
				(format "[%s]" opthead))))
  (when (LaTeX-label environment 'environment)
    (LaTeX-newline)
    (indent-according-to-mode)))

;; Needed for auto-parsing
(require 'tex)

;; Setup parsing for \newtheorem
(TeX-auto-add-type "theorem-newtheorem" "LaTeX")

(defun LaTeX-theorem-auto-prepare ()
  "Clear `LaTeX-auto-theorem-newtheorem' before parsing."
  (setq LaTeX-auto-theorem-newtheorem nil))

(defun LaTeX-theorem-auto-cleanup ()
  "Move parsed results from `LaTeX-auto-theorem-newtheorem' and
make them available as new environments."
  (dolist (newthm (mapcar 'car (LaTeX-theorem-newtheorem-list)))
    (LaTeX-add-environments (list newthm 'LaTeX-theorem-env-label))))

(add-hook 'TeX-auto-prepare-hook #'LaTeX-theorem-auto-prepare t)
(add-hook 'TeX-auto-cleanup-hook #'LaTeX-theorem-auto-cleanup t)
(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)

(TeX-add-style-hook
 "theorem"
 (lambda ()

   (TeX-auto-add-regexp
    `(,(concat "\\\\newtheorem{\\(" TeX-token-char "+\\)}")
      1 LaTeX-auto-theorem-newtheorem))

   (TeX-add-symbols
    ;; Overrule the defintion in `latex.el':
    '("newtheorem"
      (TeX-arg-eval
       (lambda ()
	 (let ((nthm (TeX-read-string
		      (TeX-argument-prompt nil nil "Environment"))))
	   (LaTeX-add-theorem-newtheorems nthm)
	   (LaTeX-add-environments (list nthm 'LaTeX-theorem-env-label))
	   (format "%s" nthm))))
      [ TeX-arg-environment "Numbered like" ]
      t [ (TeX-arg-eval progn (if (eq (save-excursion
					(backward-char 2)
					(preceding-char)) ?\])
				  ()
				(TeX-arg-counter t "Within counter"))
			"") ])

    '("theoremstyle"
      (TeX-arg-eval completing-read
		    "Style: "
		    LaTeX-theorem-theoremstyle-list))

    '("theorembodyfont"
      (LaTeX-arg-theorem-fontdecl "Body font"))

    '("theoremheaderfont"
      (LaTeX-arg-theorem-fontdecl "Header font"))

    '("theorempreskipamount"
      (TeX-arg-length "Skip before theorem"))

    '("theorempostskipamount"
      (TeX-arg-length "Skip after theorem")))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("theoremstyle"          "{")
				("theorembodyfont"       "{")
				("theoremheaderfont"     "{")
				("theorempreskipamount"  "{")
				("theorempostskipamount" "{"))
			      'function)))
 LaTeX-dialect)

(defvar LaTeX-theorem-package-options nil
  "Package options for the theorem package.")

;;; theorem.el ends here
