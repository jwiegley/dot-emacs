;;; ntheorem.el --- AUCTeX style for `ntheorem.sty' (v1.33)

;; Copyright (C) 2015, 2016 Free Software Foundation, Inc.

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

;; This file adds support for `ntheorem.sty' (v1.33) from 2011/08/15.
;; `ntheorem.sty' is and part of TeXLive.

;; The style provides the function `LaTeX-ntheorem-env-label' which
;; enables new defined environments with "\newtheoreom" to interact
;; with AUCTeX and RefTeX mechanisms for inserting labels.  Check
;; docstring of `LaTeX-ntheorem-env-label' for instructions.

;;; Code

(defvar LaTeX-ntheorem-theoremstyle-list
  '(("plain") ("break") ("change") ("changebreak") ("margin")
    ("marginbreak") ("nonumberplain") ("nonumberbreak") ("empty"))
  "List of theorem styles provided by `ntheorem.el' and new ones
defined with \"\\newtheoremstyle\".")

(defvar LaTeX-ntheorem-listtype-list
  '(("all") ("allname") ("opt") ("optname"))
  "List of predefined formatting options available for
\"\\theoremlisttype\" provided by `ntheorem.el' and new ones
defined with \"\\newtheoremlisttype\".")

(defvar LaTeX-ntheorem-fontdecl
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

(defun LaTeX-arg-ntheorem-fontdecl (optional &optional prompt)
  "Prompt for font declaration commands in \"\\theorem(body\|header)font\".
If OPTIONAL is non-nil, insert the resulting value as an optional
argument.  Use PROMPT as the prompt string."
  ;; `INITIAL-INPUT' (5th argument to `TeX-completing-read-multiple')
  ;; is hard-coded to `TeX-esc'.
  (let* ((crm-separator (regexp-quote TeX-esc))
	 (fontdecl (mapconcat 'identity
			      (TeX-completing-read-multiple
			       (TeX-argument-prompt optional prompt "Font declaration")
			       LaTeX-ntheorem-fontdecl nil nil TeX-esc)
			      TeX-esc)))
    (TeX-argument-insert fontdecl optional)))

(defun LaTeX-ntheorem-env-label (environment)
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
(TeX-auto-add-type "ntheorem-newtheorem" "LaTeX")

;; Setup parsing for \newtheoremstyle
(TeX-auto-add-type "ntheorem-newtheoremstyle" "LaTeX")

;; Setup parsing for \newtheoremlisttype
(TeX-auto-add-type "ntheorem-newtheoremlisttype" "LaTeX")

(defun LaTeX-ntheorem-auto-prepare ()
  "Clear `LaTeX-auto-ntheorem-newtheorem' and
`LaTeX-auto-ntheorem-newtheoremstyle' before parsing."
  (setq LaTeX-auto-ntheorem-newtheorem nil)
  (setq LaTeX-auto-ntheorem-newtheoremstyle nil)
  (setq LaTeX-auto-ntheorem-newtheoremlisttype nil))

(defun LaTeX-ntheorem-auto-cleanup ()
  "Move parsed results from `LaTeX-auto-ntheorem-newtheorem' and
make them available as new environments.  Update
`LaTeX-ntheorem-theoremstyle-list' with styles defined with
\"\\newtheoremstyle\"."
  (dolist (newthm (mapcar 'car (LaTeX-ntheorem-newtheorem-list)))
    (LaTeX-add-environments (list newthm 'LaTeX-ntheorem-env-label))
    (LaTeX-add-environments (list (concat newthm "*")
				  'LaTeX-ntheorem-env-label)))
  (dolist (newthmstyle (LaTeX-ntheorem-newtheoremstyle-list))
    (add-to-list (make-local-variable 'LaTeX-ntheorem-theoremstyle-list)
		 newthmstyle))
  (dolist (newthmlist (LaTeX-ntheorem-newtheoremlisttype-list))
    (add-to-list (make-local-variable 'LaTeX-ntheorem-listtype-list)
		 newthmlist))
  (when (LaTeX-provided-package-options-member "ntheorem" "thmmarks")
    (dolist (nthm (mapcar 'car (LaTeX-ntheorem-newtheorem-list)))
      (TeX-add-symbols (concat nthm "Symbol"))))
  (dolist (nthm (mapcar 'car (LaTeX-ntheorem-newtheorem-list)))
    (TeX-add-symbols (concat nthm "name"))))

(add-hook 'TeX-auto-prepare-hook #'LaTeX-ntheorem-auto-prepare t)
(add-hook 'TeX-auto-cleanup-hook #'LaTeX-ntheorem-auto-cleanup t)
(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)

(TeX-add-style-hook
 "ntheorem"
 (lambda ()

   (TeX-auto-add-regexp
    `(,(concat "\\\\newtheorem{\\(" TeX-token-char "+\\)}")
      1 LaTeX-auto-ntheorem-newtheorem))
   (TeX-auto-add-regexp
    `(,(concat "\\\\newframedtheorem{\\(" TeX-token-char "+\\)}")
      1 LaTeX-auto-ntheorem-newtheorem))
   (TeX-auto-add-regexp
    `(,(concat "\\\\newshadedtheorem{\\(" TeX-token-char "+\\)}")
      1 LaTeX-auto-ntheorem-newtheorem))
   (TeX-auto-add-regexp
    `(,(concat "\\\\newtheoremstyle{\\(" TeX-token-char "+\\)}")
      1 LaTeX-auto-ntheorem-newtheoremstyle))
   (TeX-auto-add-regexp
    `(,(concat "\\\\newtheoremlisttype{\\(" TeX-token-char "+\\)}")
      1 LaTeX-auto-ntheorem-newtheoremlisttype))

   (TeX-add-symbols
    ;; 2.2 Defining New Theorem Sets
    ;; Overrule the defintion in `latex.el':
    '("newtheorem"
      (TeX-arg-eval
       (lambda ()
	 (let ((nthm (TeX-read-string
		      (TeX-argument-prompt nil nil "Environment"))))
	   (LaTeX-add-ntheorem-newtheorems nthm)
	   (LaTeX-add-environments (list nthm 'LaTeX-ntheorem-env-label))
	   (LaTeX-add-environments (list (concat nthm "*")
					 'LaTeX-ntheorem-env-label))
	   (format "%s" nthm))))
      [ TeX-arg-environment "Numbered like" ]
      t [ (TeX-arg-eval progn (if (eq (save-excursion
					(backward-char 2)
					(preceding-char)) ?\])
				  ()
				(TeX-arg-counter t "Within counter"))
			"") ])

    '("renewtheorem"
      (TeX-arg-eval completing-read "Environment: "
		    (LaTeX-ntheorem-newtheorem-list))
      [ TeX-arg-environment "Numbered like" ]
      t [ (TeX-arg-eval progn (if (eq (save-excursion
					(backward-char 2)
					(preceding-char)) ?\])
				  ()
				(TeX-arg-counter t "Within counter"))
			"") ])

    ;; 2.3 Defining the Layout of Theorem Sets
    '("theoremstyle"
      (TeX-arg-eval completing-read "Style: "
		    LaTeX-ntheorem-theoremstyle-list))

    '("theorembodyfont"
      (LaTeX-arg-ntheorem-fontdecl "Body font"))

    '("theoremheaderfont"
      (LaTeX-arg-ntheorem-fontdecl "Header font"))

    '("theoremnumbering"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Numbering scheme")
		    '("arabic" "roman" "Roman" "alph" "Alph"
		      "greek" "Greek" "fnsymbol")))

    '("theoremseparator" "Separator")

    '("theorempreskip"
      (TeX-arg-length "Skip before theorem"))

    '("theorempostskip"
      (TeX-arg-length "Skip after theorem"))

    '("theoremindent"
      (TeX-arg-free "Theorem indent"))

    (when (LaTeX-provided-package-options-member "ntheorem" "thmmarks")
      '("theoremsymbol" t))

    '("theoremprework" t)
    '("theorempostwork" t)

    '("theoremclass"
      (TeX-arg-eval completing-read "Theorem type: "
		    (append '(("LaTeX"))
			    (LaTeX-ntheorem-newtheorem-list))))

    ;; 2.3.6 A Standard Set of Theorems
    (when (LaTeX-provided-package-options-member "ntheorem" "standard")
      (let ((env '("Theorem"    "Lemma"     "Proposition"
		   "Corollary"  "Satz"      "Korollar"
		   "Definition" "Example"   "Beispiel"
		   "Anmerkung"  "Bemerkung" "Remark"
		   "Proof"      "Beweis")))
	(dolist (elt env)
	  (LaTeX-add-ntheorem-newtheorems elt)
	  (LaTeX-add-environments (list elt 'LaTeX-ntheorem-env-label))
	  (LaTeX-add-environments (list (concat elt "*")
					'LaTeX-ntheorem-env-label)))))

    ;; 2.3.7 Framed and Boxed Theorems
    '("newframedtheorem"
      (TeX-arg-eval
       (lambda ()
	 (let ((nthm (TeX-read-string
		      (TeX-argument-prompt nil nil "Environment"))))
	   (LaTeX-add-ntheorem-newtheorems nthm)
	   (LaTeX-add-environments (list nthm 'LaTeX-ntheorem-env-label))
	   (LaTeX-add-environments (list (concat nthm "*")
					 'LaTeX-ntheorem-env-label))
	   (format "%s" nthm))))
      [ TeX-arg-environment "Numbered like" ]
      t [ (TeX-arg-eval progn (if (eq (save-excursion
					(backward-char 2)
					(preceding-char)) ?\])
				  ()
				(TeX-arg-counter t "Within counter"))
			"") ])

    '("newshadedtheorem"
      (TeX-arg-eval
       (lambda ()
	 (let ((nthm (TeX-read-string
		      (TeX-argument-prompt nil nil "Environment"))))
	   (LaTeX-add-ntheorem-newtheorems nthm)
	   (LaTeX-add-environments (list nthm 'LaTeX-ntheorem-env-label))
	   (LaTeX-add-environments (list (concat nthm "*")
					 'LaTeX-ntheorem-env-label))
	   (format "%s" nthm))))
      [ TeX-arg-environment "Numbered like" ]
      t [ (TeX-arg-eval progn (if (eq (save-excursion
					(backward-char 2)
					(preceding-char)) ?\])
				  ()
				(TeX-arg-counter t "Within counter"))
			"") ])
    '("shadecolor"
      (TeX-arg-eval
       (lambda ()
	 (let ((color (cond ((member "xcolor" (TeX-style-list))
			     (completing-read "Color name: " (LaTeX-xcolor-definecolor-list)))
			    ((member "color" (TeX-style-list))
			     (completing-read "Color name: " (LaTeX-color-definecolor-list)))
			    (t
			     (TeX-read-string "Color name: ")))))
	   (format "%s" color)))))

    '("theoremframepreskip"
      (TeX-arg-length "Skip before framed theorem"))

    '("theoremframepostskip"
      (TeX-arg-length "Skip after framed theorem"))

    '("theoreminframepreskip"
      (TeX-arg-length "Skip inside framed theorem"))

    '("theoreminframepostskip"
      (TeX-arg-length "Skip inside framed theorem"))

    ;; 2.4 Generating Theoremlists
    '("listtheorems"
      (TeX-arg-eval mapconcat 'identity
		    (TeX-completing-read-multiple
		     "Lists: "
		     (LaTeX-ntheorem-newtheorem-list)) ","))

    ;; 2.4.2 Writing Extra Stuff to the Theorem File
    '("addtheoremline"
      (TeX-arg-eval completing-read "Environment: "
		    (LaTeX-ntheorem-newtheorem-list))
      t)

    '("addtheoremline*"
      (TeX-arg-eval completing-read "Environment: "
		    (LaTeX-ntheorem-newtheorem-list))
      t)

    '("addtotheoremfile"
      [ TeX-arg-eval completing-read "Environment: "
		     (LaTeX-ntheorem-newtheorem-list) ]
      t)

    ;; 2.5.1 Defining New Theorem Layouts
    '("newtheoremstyle"
      (TeX-arg-eval
       (lambda ()
	 (let ((style (TeX-read-string
		       (TeX-argument-prompt optional nil "Style name"))))
	   (LaTeX-add-ntheorem-newtheoremstyles style)
	   (add-to-list (make-local-variable 'LaTeX-ntheorem-theoremstyle-list)
			(list style))
	   (format "%s" style))))
      2)

    '("renewtheoremstyle"
      (TeX-arg-eval completing-read "Style name: "
		    LaTeX-ntheorem-theoremstyle-list)
      2)

    ;; 2.5.2 Defining New Theorem List Layouts
    '("newtheoremlisttype"
      (TeX-arg-eval
       (lambda ()
	 (let ((layout (TeX-read-string
		       (TeX-argument-prompt optional nil "List layout name"))))
	   (LaTeX-add-ntheorem-newtheoremlisttypes layout)
	   (add-to-list (make-local-variable 'LaTeX-ntheorem-listtype-list)
			(list layout))
	   (format "%s" layout))))
      3)

    '("renewtheoremlisttype"
      (TeX-arg-eval completing-read "Style name: "
		    LaTeX-ntheorem-listtype-list)
      3)

    ;; 2.6 Setting End Marks
    '("qedsymbol" t)
    '("NoEndMark" 0)

    ;; 2.7 Extended Referencing Features
    (when (LaTeX-provided-package-options-member "ntheorem" "thref")
      '("thref" TeX-arg-ref)) )

   ;; 2.6 Setting End Marks
   ;; ... the endmark can manually be set by just saying \<name>Symbol.
   (when (LaTeX-provided-package-options-member "ntheorem" "thmmarks")
     (dolist (nthm (mapcar 'car (LaTeX-ntheorem-newtheorem-list)))
       (TeX-add-symbols (concat nthm "Symbol"))))

   ;; 2.8 Miscellaneous
   ;; Inside a theorem-like environment <env>, the name given as
   ;; optional argument is accessible by \<env>name
   (dolist (nthm (mapcar 'car (LaTeX-ntheorem-newtheorem-list)))
     (TeX-add-symbols (concat nthm "name")))

;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("newtheorem"             "{[{[")
				("renewtheorem"           "{[{[")
				("theoremstyle"           "{")
				("theorembodyfont"        "{")
				("theoremheaderfont"      "{")
				("theoremnumbering"       "{")
				("theoremseparator"       "{")
				("theorempreskip"         "{")
				("theorempostskip"        "{")
				("theoremsymbol"          "{")
				("theoremindent"          "")
				("theoremprework"         "{")
				("theorempostwork"        "{")
				("theoremclass"           "{")
				("newframedtheorem"       "{[{[")
				("newshadedtheorem"       "*{[{[")
				("shadecolor"             "{")
				("theoremframepreskip"    "{")
				("theoremframepostskip"   "{")
				("theoreminframepreskip"  "{")
				("theoreminframepostskip" "{")
				("listtheorems"           "{")
				("addtheoremline"         "*{{")
				("addtotheoremfile"       "[{")
				("newtheoremstyle"        "{{{")
				("renewtheoremstyle"      "{{{")
				("newtheoremlisttype"     "{{{{")
				("renewtheoremlisttype"   "{{{{"))
			      'function)
     (font-latex-add-keywords '(("thref"                  "{"))
			      'reference)))
 LaTeX-dialect)

(defvar LaTeX-ntheorem-package-options
  '("standard" "noconfig" "framed" "thmmarks" "thref" "amsmath" "hyperref")
  "Package options for the ntheorem package.")

;;; ntheorem.el ends here
