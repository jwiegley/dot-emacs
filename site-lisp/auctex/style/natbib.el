;;; natbib.el --- AUCTeX style for `natbib.sty' version 8.31b

;; Copyright (C) 1997, 1998, 2004, 2007, 2014, 2016 Free Software Foundation, Inc.

;; Authors: Berwin Turlach <statba@nus.edu.sg>
;;          Carsten Dominik <dominik@strw.leidenuniv.nl>
;; Maintainer: auctex-devel@gnu.org
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

;;; Code:

(TeX-add-style-hook
 "natbib"
 (lambda ()
   ;; The number in the cdr of the following list indicates how many
   ;; optional note arguments we consider useful.  Prompting for those
   ;; arguments will still depend upon `TeX-arg-cite-note-p'.
   (let  ((citecmds
	   '(("cite" . 0)
	     ("citet" . 1) ("citet*" . 1) ("citealt" . 1) ("citealt*" . 1)
	     ("citep" . 2) ("citep*" . 2) ("citealp" . 2) ("citealp*" . 2)
	     ("citeauthor" . 0) ("citeauthor*" . 0) ("citefullauthor" . 0)
	     ("citeyear" . 0) ("citeyearpar" . 0)
	     ("shortcites" . 0)
	     ;; 2.4 Extended Citation Commands
	     ("citenum" . 0)
	     ;; 2.5 Forcing Upper Cased Name
	     ("Citet" . 1) ("Citet*" . 1) ("Citealt" . 1) ("Citealt*" . 1)
	     ("Citep" . 2) ("Citep*" . 2) ("Citealp" . 2) ("Citealp*" . 2)
	     ;; 2.6 Citation Aliasing
	     ("citetalias" . 1) ("citepalias" . 2))))

     ;; Add these symbols
     (apply
      #'TeX-add-symbols
      (mapcar
       (lambda (cmd)
	 (cond
	  ((= (cdr cmd) 0)
	   ;; No optional arguments
	   (list (car cmd) 'TeX-arg-cite))
	  ((= (cdr cmd) 1)
	   ;; Just one optional argument, the post note
	   (list
	    (car cmd)
	    '(TeX-arg-conditional TeX-arg-cite-note-p (["Post-note"]) nil)
	    'TeX-arg-cite))
	  ((= (cdr cmd) 2)
	   ;; Pre and post notes
	   (list
	    (car cmd)
	    '(TeX-arg-conditional TeX-arg-cite-note-p ([LaTeX-arg-natbib-notes]) nil)
	    'TeX-arg-cite))))
       citecmds))

     ;; Make an entry in TeX-complete-list
     (add-to-list
      'TeX-complete-list
      (list
       (concat "\\\\\\("
	       (mapconcat (lambda (x) (regexp-quote (car x)))
			  citecmds "\\|")
	       "\\)\\(\\[[^]\n\r\\%]*\\]\\)*{\\([^{}\n\r\\%,]*,\\)*\\([^{}\n\r\\%,]*\\)")
       4 'LaTeX-bibitem-list "}")))

   ;; Add the other symbols
   (TeX-add-symbols
    ;; 2.4 Extended Citation Commands
    '("citetext" "Text")

    ;; 2.6 Citation Aliasing
    '("defcitealias" TeX-arg-cite "Alias")

    ;; 2.9 Selecting Citation Punctuation
    '("setcitestyle" (TeX-arg-key-val
		      (;; Citation mode (fourth argument of \bibpunct):
		       ("authoryear") ("numbers") ("super")
		       ;; Braces (first and second arguments of \bibpunct):
		       ("round") ("square") ("open") ("close")
		       ;; Between citations (third argument of \bibpunct):
		       ("semicolon") ("comma") ("citesep")
		       ;; Between author and year (fifth argument of \bibpunct):
		       ("aysep")
		       ;; Between years with common author (sixth argument of \bibpunct):
		       ("yysep")
		       ;; Text before post-note (optional argument of \bibpunct):
		       ("notesep"))))
    '("bibpunct" ["Post note separator"]
      "Opening bracket"
      "Closing bracket"
      "Punctuation between multiple citations"
      "style [n]umeric [s]uperscript [a]uthor-year"
      "Punctuation between author and year"
      "Punctuation between years for common authors")

    '("citestyle" (TeX-arg-eval completing-read
				(TeX-argument-prompt optional nil "Style")
				'("plain" "plainnat" "agu" "egu"
				  "agms" "dcu" "kluwer" "cospar" "nature")))

    ;; 2.12 Other Formatting Options
    "bibsection"
    "bibpreamble"
    "bibfont"
    "citenumfont"
    "bibnumfmt"

    ;; 2.13 Automatic Indexing of Citations
    '("citeindextrue")
    '("citeindexfalse")
    '("citeindextype"))

   ;; 2.12 Other Formatting Options
   (LaTeX-add-lengths "bibhang" "bibsep")

   ;; Fontification
   (when (and (fboundp 'font-latex-add-keywords)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("cite"           "*[[{")
				("citet"	  "*[[{")
				("citealt"	  "*[[{")
				("citep"	  "*[[{")
				("citealp"	  "*[[{")
				("citeauthor"	  "*[[{")
				("citefullauthor" "[[{")
				("citeyear"	  "[[{")
				("citeyearpar"	  "[[{")
				("shortcites"     "{")
				("citenum"        "{")
				("Citet"	  "*[[{")
				("Citealt"	  "*[[{")
				("Citep"	  "*[[{")
				("Citealp"	  "*[[{")
				("Citeauthor"	  "*[[{")
				("citetalias"	  "*[[{")
				("citepalias"	  "*[[{"))
			      'reference)
     (font-latex-add-keywords '(("defcitealias"   "{{")
				("bibpunct"	  "[{{{{{{")
				("setcitestyle"   "{")
				("citestyle"	  "{"))
			      'function))

   ;; Tell RefTeX
   (when (and LaTeX-reftex-cite-format-auto-activate
	      (fboundp 'reftex-set-cite-format))
     (reftex-set-cite-format 'natbib)))
 LaTeX-dialect)

(defun LaTeX-arg-natbib-notes (optional)
  "Prompt for two note arguments a natbib citation command.
If OPTIONAL is non-nil, insert them in brackets, otherwise in
braces."
  (let ((pre (TeX-read-string
	      (TeX-argument-prompt optional nil "Pre-note")))
	(post (TeX-read-string
	       (TeX-argument-prompt optional nil "Post-note"))))
    (TeX-argument-insert pre optional)
    (TeX-argument-insert post optional)
    ;; pre is given, post is empty: Make sure that we insert an
    ;; extra pair of `[]', otherwise pre becomes post
    (when (and pre (not (string= pre ""))
	       (string= post ""))
      (insert LaTeX-optop LaTeX-optcl))))

(defvar LaTeX-natbib-package-options '("numbers" "super" "authoryear"
				       "round" "square" "angle" "curly"
				       "comma" "colon" "nobibstyle"
				       "bibstyle" "openbib" "sectionbib"
				       "sort" "sort&compress"
				       "longnamesfirst" "nonamebreak")
  "Package options for the natbib package.")

;; natbib.el ends here
