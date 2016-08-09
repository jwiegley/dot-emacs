;;; subcaption.el --- AUCTeX style for `subcaption.sty' (v1.1-100)

;; Copyright (C) 2015 Free Software Foundation, Inc.

;; Author: Arash Esbati <esbati'at'gmx.de>
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

;; This file adds support for `subcaption.sty' (v1.1-100) from
;; 2015-09-15.  `subcaption.sty' is part of TeXLive.

;;; Code:

(defvar LaTeX-subcaption-key-val-options
  '(("subrefformat" ("default" "empty" "simple" "brace" "parens")))
  "Key=value options for subcaption package.  This key takes the
same values as \"labelformat\" from caption package.")

(defun LaTeX-arg-subcaption-subcaption (optional &optional star prompt)
  "Query for the arguments of \\subcaption incl. a label and
insert them.  If STAR is non-nil, then do not query for the lof entry
and \\label and insert only a caption."
  (let ((lof (unless star
	       (TeX-read-string
		(TeX-argument-prompt t prompt "List entry"))))
	(caption (TeX-read-string
		  (TeX-argument-prompt optional prompt "Sub-caption"))))
    (LaTeX-indent-line)
    (when (and lof (not (string-equal lof "")))
      (insert LaTeX-optop lof LaTeX-optcl))
    (insert TeX-grop caption TeX-grcl)
    (unless star
      (LaTeX-newline)
      (LaTeX-indent-line)
      (TeX-insert-macro "label"))))

(defun LaTeX-arg-subcaption-subcaptionbox (optional &optional star prompt)
  "Query for the arguments of \\subcaptionbox incl. a label and
insert them.  If STAR is non-nil, then do not query for a \\label and
insert only a caption."
  (let ((caption (TeX-read-string
		  (TeX-argument-prompt optional prompt "Sub-caption"))))
    (LaTeX-indent-line)
    (insert TeX-grop caption)
    (unless star (TeX-insert-macro "label"))
    (insert TeX-grcl))
  (let* ((width (completing-read (TeX-argument-prompt t prompt "Width")
				 (mapcar (lambda (elt) (concat TeX-esc (car elt)))
					 (LaTeX-length-list))))
	 (inpos (when (and width (not (string-equal width "")))
		  (completing-read (TeX-argument-prompt t prompt "Inner position")
				   '("c" "l" "r" "s")))))
    (cond (;; 2 optional args
	   (and width (not (string-equal width ""))
		inpos (not (string-equal inpos "")))
	   (insert (format "[%s][%s]" width inpos)))
	  (;; 1st opt. arg, 2nd empty opt. arg
	   (and width (not (string-equal width ""))
		(string-equal inpos ""))
	   (insert (format "[%s]" width)))
	  (t ; Do nothing if both empty
	   (ignore)))))

(TeX-add-style-hook
 "subcaption"
 (lambda ()
   ;; Run style hook for caption.el
   (TeX-run-style-hooks "caption")

   ;; Make "subrefformat" available in key-vals of caption.el:
   (setq LaTeX-caption-key-val-options-local
	 (append LaTeX-subcaption-key-val-options
		 LaTeX-caption-key-val-options-local))

   (TeX-add-symbols
    ;; Basic commands
    '("subcaption"     (LaTeX-arg-subcaption-subcaption))
    '("subcaption*"    (LaTeX-arg-subcaption-subcaption t))
    '("subcaptionbox"  ["List entry"] (LaTeX-arg-subcaption-subcaptionbox) t)
    '("subcaptionbox*" (LaTeX-arg-subcaption-subcaptionbox t) t)
    '("subref"         TeX-arg-ref)
    ;; \subref* is only available with hyperref.sty loaded, we don't
    ;; check if hyperref.el is loaded and make it available directly.
    '("subref*"        TeX-arg-ref)
    '("phantomcaption"    0)
    '("phantomsubcaption" 0))

   ;; The next 2 macros are part of the kernel of caption.sty, but we
   ;; load them within subcaption.el.
   (TeX-add-symbols
    '("DeclareCaptionSubType"
      [TeX-arg-eval
       completing-read (TeX-argument-prompt t nil "Numbering scheme")
       '("arabic" "roman" "Roman" "alph" "Alph" "fnsymbol")]
      (TeX-arg-eval
       completing-read (TeX-argument-prompt nil nil "Type")
       '("figure" "table")))

    '("DeclareCaptionSubType*"
      [TeX-arg-eval completing-read
		    (TeX-argument-prompt t nil "Numbering scheme")
		    '("arabic" "roman" "Roman" "alph" "Alph" "fnsymbol")]
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt nil nil "Type")
		    '("figure" "table"))))

   ;; The subfigure & subtable environments
   (LaTeX-add-environments
    '("subfigure" LaTeX-env-minipage)
    '("subtable"  LaTeX-env-minipage))

   ;; Introduce env's to RefTeX if loaded
   (when (fboundp 'reftex-add-label-environments)
     (reftex-add-label-environments
      `(("subfigure" ?f ,LaTeX-figure-label "~\\ref{%s}" caption)
	("subtable"  ?t ,LaTeX-table-label  "~\\ref{%s}" caption))))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("subcaption"            "*[{")
				("subcaptionbox"         "*[{[[{")
				("phantomcaption"        "")
				("phantomsubcaption"     ""))
			      'textual)
     (font-latex-add-keywords '(("subref"                "*{"))
			      'reference)
     (font-latex-add-keywords '(("DeclareCaptionSubType" "*[{"))
			      'function)) )
 LaTeX-dialect)

(defun LaTeX-subcaption-package-options ()
  "Prompt for package options for the subcaption package."
  (TeX-read-key-val t
   (append LaTeX-subcaption-key-val-options
	   LaTeX-caption-key-val-options)))

;;; subcaption.el ends here
