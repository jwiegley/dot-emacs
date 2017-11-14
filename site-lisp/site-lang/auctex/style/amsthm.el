;;; amsthm.el --- Style hook for the AMS-LaTeX amsthm package.

;; Copyright (C) 1997, 2013--2015 Free Software Foundation, Inc.

;; Author: Carsten Dominik <dominik@strw.leidenuniv.nl>
;; Maintainer: auctex-devel@gnu.org

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

;; The style provides the function `LaTeX-amsthm-env-label' which
;; enables new defined environments with "\newtheoreom" to interact
;; with AUCTeX and RefTeX mechanisms for inserting labels.  Check
;; docstring of `LaTeX-amsthm-env-label' for instructions.

;;; Code:

(defvar LaTeX-amsthm-package-options nil
  "Package options for the amsthm package.")

(defvar LaTeX-amsthm-theoremstyle-list
  '(("plain") ("definition") ("remark"))
  "List of theorem styles provided by `amsthm.el' and new ones
defined with \"\\newtheoremstyle\".")

(defvar LaTeX-amsthm-fontdecl
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
  "List of font declaration commands for \"\\newtheoremstyle\".")

(defun LaTeX-arg-amsthm-fontdecl (optional &optional prompt)
  "Prompt for font declaration commands in \"\\newtheoremstyle\".
If OPTIONAL is non-nil, insert the resulting value as an optional
argument.  Use PROMPT as the prompt string."
  ;; `INITIAL-INPUT' (5th argument to `TeX-completing-read-multiple')
  ;; is hard-coded to `TeX-esc'.
  (let* ((crm-separator (regexp-quote TeX-esc))
	 (fontdecl (mapconcat 'identity
			      (TeX-completing-read-multiple
			       (TeX-argument-prompt optional prompt "Font")
			       LaTeX-amsthm-fontdecl nil nil TeX-esc)
			      TeX-esc)))
    (TeX-argument-insert fontdecl optional)))

(defun LaTeX-amsthm-env-label (environment)
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
(TeX-auto-add-type "amsthm-newtheorem" "LaTeX")

;; Setup parsing for \newtheoremstyle
(TeX-auto-add-type "amsthm-newtheoremstyle" "LaTeX")

(defun LaTeX-amsthm-auto-prepare ()
  "Clear `LaTeX-auto-amsthm-newtheorem' and
`LaTeX-auto-amsthm-newtheoremstyle' before parsing."
  (setq LaTeX-auto-amsthm-newtheorem nil)
  (setq LaTeX-auto-amsthm-newtheoremstyle nil))

(defun LaTeX-amsthm-auto-cleanup ()
  "Move parsed results from `LaTeX-auto-amsthm-newtheorem' and
make them available as new environments.  Update
`LaTeX-amsthm-theoremstyle-list' with styles defined with
\"\\newtheoremstyle\"."
  (dolist (newthm (mapcar 'car (LaTeX-amsthm-newtheorem-list)))
    (LaTeX-add-environments (list newthm 'LaTeX-amsthm-env-label)))
  (dolist (newthmstyle (LaTeX-amsthm-newtheoremstyle-list))
    (add-to-list (make-local-variable 'LaTeX-amsthm-theoremstyle-list)
		 newthmstyle)))

(add-hook 'TeX-auto-prepare-hook #'LaTeX-amsthm-auto-prepare t)
(add-hook 'TeX-auto-cleanup-hook #'LaTeX-amsthm-auto-cleanup t)
(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)

(TeX-add-style-hook
 "amsthm"
 (lambda ()
   (LaTeX-add-environments
    '("proof" LaTeX-amsthm-env-label))
   (TeX-add-symbols
    ;; Overrule the defintion in `latex.el':
    '("newtheorem"
      (TeX-arg-eval
       (lambda ()
	 (let ((nthm (TeX-read-string
		      (TeX-argument-prompt nil nil "Environment"))))
	   (LaTeX-add-amsthm-newtheorems nthm)
	   (LaTeX-add-environments (list nthm 'LaTeX-theorem-env-label))
	   (format "%s" nthm))))
      [ TeX-arg-environment "Numbered like" ]
      t [ (TeX-arg-eval progn (if (eq (save-excursion
					(backward-char 2)
					(preceding-char)) ?\])
				  ()
				(TeX-arg-counter t "Within counter"))
			"") ])

    '("newtheorem*"
      (TeX-arg-eval
       (lambda ()
	 (let ((nthm (TeX-read-string
		      (TeX-argument-prompt nil nil "Environment")))
	       (heading (TeX-read-string
			 (TeX-argument-prompt nil nil "Heading"))))
	   (LaTeX-add-amsthm-newtheorems nthm)
	   (LaTeX-add-environments (list nthm 'LaTeX-amsthm-env-label))
	   (insert (concat TeX-grop nthm TeX-grcl))
	   (format "%s" heading)))))

    '("theoremstyle"
      (TeX-arg-eval completing-read "Style: "
		    LaTeX-amsthm-theoremstyle-list))
    "qedhere"
    "swapnumbers"

    '("newtheoremstyle"
      (TeX-arg-eval
       (lambda ()
	 (let ((nthmstyle (TeX-read-string
			   (TeX-argument-prompt nil nil "Style name"))))
	   (LaTeX-add-amsthm-newtheoremstyles nthmstyle)
	   (add-to-list (make-local-variable 'LaTeX-amsthm-theoremstyle-list)
			(list nthmstyle))
	   (format "%s" nthmstyle))))
      (TeX-arg-length "Space above")
      (TeX-arg-length "Space below")
      (LaTeX-arg-amsthm-fontdecl "Body font")
      "Indent amount"
      (LaTeX-arg-amsthm-fontdecl "Theorem head font")
      "Punctuation after head"
      (TeX-arg-length "Space after head")
      "Theorem head spec"))

   (TeX-auto-add-regexp
    `(,(concat "\\\\newtheorem\\*?{\\(" TeX-token-char "+\\)}")
      1 LaTeX-auto-amsthm-newtheorem))
   (TeX-auto-add-regexp
    `(,(concat "\\\\newtheoremstyle{\\(" TeX-token-char "+\\)}")
      1 LaTeX-auto-amsthm-newtheoremstyle))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("newtheorem"      "*{[{[")
				("theoremstyle"    "{")
				("newtheoremstyle" "{{{{{{{{{"))
			      'function)))
 LaTeX-dialect)

;;; amsthm.el ends here
