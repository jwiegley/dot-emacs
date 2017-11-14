;;; splitidx.el --- AUCTeX style for `splitidx.sty' (v1.2a)

;; Copyright (C) 2016 Free Software Foundation, Inc.

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

;; This file adds support for `splitidx.sty' (v1.2a) from 2013/04/09.
;; `splitidx.sty' is part of TeXLive.

;; The main index macro provided by `splitidx.sty' is
;;
;;     \sindex[<shortcut>]{<index-entry>}
;;
;; where <shortcut> identifies the target where <index-entry> is going
;; into.  This style checks if RefTeX is loaded and adds "\sindex" to
;; index macros known by RefTeX; this is described in RefTeX manual
;; section 5.5 Defining Index Macros:
;;
;;     (setq reftex-index-macros '(("\\sindex[]{*}" 1 ?s "" nil t)))
;;
;; To make things more user friendly, this style does not hard-code
;; the key `?s' and offers a customizable variable called
;; `LaTeX-splitidx-sindex-reftex-quick-id-key'.  Customize this
;; variable to another unique key if you have other preference.  Also
;; note the integer 1 after "\\sindex[]{*}".  This tells RefTeX to
;; look in first optional argument to find out which index the entry
;; belongs to.  If omitted, RefTeX puts the index entry into "idx".

;; `splitidx.sty' provides also the option `idxcommands' where a
;; command with the name of the <shortcut> is defined for each
;; declared index.  An example from splitidx.pdf:
;;
;;     \documentclass{article}
;;     \usepackage[idxcommands]{splitidx}
;;
;;     \newindex[General Index]{idx}       % Name and shortcut of the 1st index
;;     \newindex[Index of Animals]{ani}    % ... 2nd index
;;     \newindex[Index of Fruits]{fru}     % ... 3rd index
;;     \newindex[Index of Vegetables]{veg} % ... 4th index
;;     ...
;;
;; Now four index commands \idx, \ani, \fru and \veg are available.
;; This style adds these commands to AUCTeX and RefTeX (check function
;; `LaTeX-splitidx-auto-cleanup').  The only thing missing is adding
;; these commands to `reftex-index-macros' since the unique keys must
;; be set by user.  To get full advantage from RefTeX, remember that
;; ?i, ?I, and ?g are reserved and set something like this in your
;; init-file:
;;
;;     (add-to-list 'reftex-index-macros '("\\idx" "idx" ?x "" nil t))
;;     (add-to-list 'reftex-index-macros '("\\ani" "ani" ?a "" nil t))
;;     (add-to-list 'reftex-index-macros '("\\fru" "fru" ?f "" nil t))
;;     (add-to-list 'reftex-index-macros '("\\veg" "veg" ?v "" nil t))
;;
;; Or you can do this in your tex file:
;;
;;     %%% Local Variables:
;;     %%% mode: latex
;;     %%% TeX-master: t
;;     %%% eval: (add-to-list 'reftex-index-macros '("\\idx" "idx" ?x "" nil t))
;;     %%% eval: (add-to-list 'reftex-index-macros '("\\ani" "ani" ?a "" nil t))
;;     %%% eval: (add-to-list 'reftex-index-macros '("\\fru" "fru" ?f "" nil t))
;;     %%% eval: (add-to-list 'reftex-index-macros '("\\veg" "veg" ?v "" nil t))
;;     %%% End:
;;

;;; Code:

;; Needed for auto-parsing.
(require 'tex)

;; Setup parsing for \newindex:
(TeX-auto-add-type "splitidx-newindex" "LaTeX" "splitidx-newindices")

(defvar LaTeX-splitidx-newindex-regex
  `(,(concat "\\\\new\\(?:protected\\)?index"
	     "\\(?:\\[[^]]*\\]\\)?"
	     "{\\([^}]+\\)}")
    1 LaTeX-auto-splitidx-newindex)
  "Matches the argument of `\\newindex' from `splitidx.sty'.")

(defun LaTeX-splitidx-auto-prepare ()
  "Clear `LaTeX-auto-splitidx-newindex' before parsing."
  (setq LaTeX-auto-splitidx-newindex nil))

(defun LaTeX-splitidx-auto-cleanup ()
  "Process parsed results for \"splitidx.sty\"."
  (when (LaTeX-provided-package-options-member "splitidx" "idxcommands")
    (dolist (elt (mapcar #'car (LaTeX-splitidx-newindex-list)))
      ;; Make every element available as a command
      (TeX-add-symbols `(,elt TeX-arg-index))
      ;; Add new macros's to `ispell-tex-skip-alist': skip one argument
      (TeX-ispell-skip-setcar `((,elt ispell-tex-arg-end)))
      ;; font-locking
      (when (and (featurep 'font-latex)
		 (eq TeX-install-font-lock 'font-latex-setup))
	(font-latex-add-keywords `((,elt  "{"))
				 'reference))
      ;; Prepare for parsing
      (add-to-list 'LaTeX-auto-regexp-list
		   `(,(concat
		       "\\\\"
		       elt
		       "{\\([^}{]*\\({[^}{]*\\({[^}{]*\\({[^}{]*}[^}{]*\\)*"
		       "}[^}{]*\\)*}[^}{]*\\)*\\)}")
		     1 LaTeX-auto-index-entry))
      ;; Cater for completion
      (add-to-list 'TeX-complete-list
		   `(,(concat "\\\\" elt "{\\([^{}\n\r]*\\)")
		     1 LaTeX-index-entry-list "}")) )))

(add-hook 'TeX-auto-prepare-hook #'LaTeX-splitidx-auto-prepare t)
(add-hook 'TeX-auto-cleanup-hook #'LaTeX-splitidx-auto-cleanup t)
(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)

(TeX-add-style-hook
 "splitidx"
 (lambda ()

   (TeX-add-symbols

    ;; 3.1 Setup
    '("newindex"
      [ "Index name" ]
      (TeX-arg-eval
       (lambda ()
	 (let ((shortcut (TeX-read-string
			  (TeX-argument-prompt optional nil "Short cut"))))
	   (LaTeX-add-splitidx-newindices shortcut)
	   (format "%s" shortcut)))))

    ;; 3.2 Marking up index entries
    '("sindex"
      ;; I don't use `[ TeX-arg-index-tag ]' here
      [ TeX-arg-eval completing-read
		     (TeX-argument-prompt optional nil "Short cut")
		     (LaTeX-splitidx-newindex-list) ]
      TeX-arg-index)

    ;; 3.4 Customizing index entries
    '("AtWriteToIndex"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Short cut")
		    (LaTeX-splitidx-newindex-list))
      t)

    '("AtNextWriteToIndex"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Short cut")
		    (LaTeX-splitidx-newindex-list))
      t)

    ;; 3.6 Preventing premature expansion of index entries
    '("newprotectedindex"
      [ "Index name" ]
      (TeX-arg-eval
       (lambda ()
	 (let ((shortcut (TeX-read-string
			  (TeX-argument-prompt optional nil "Short cut"))))
	   (LaTeX-add-splitidx-newindices shortcut)
	   (format "%s" shortcut)))))

    ;; 3.7 Including the generated indices in your document
    '("printindex"
      [ TeX-arg-eval completing-read
		     (TeX-argument-prompt optional nil "Short cut")
		     (LaTeX-splitidx-newindex-list) ]
      [ "Index name" ])

    '("printindex*" 0)

    '("printsubindex"
      [ TeX-arg-eval completing-read
		     (TeX-argument-prompt optional nil "Short cut")
		     (LaTeX-splitidx-newindex-list) ]
      [ "Index name" ])

    '("printsubindex*" 0)

    '("setindexpreamble"
      [ TeX-arg-eval completing-read
		     (TeX-argument-prompt optional nil "Short cut")
		     (LaTeX-splitidx-newindex-list) ]
      t)

    '("useindexpreamble" [ TeX-arg-macro ])

    '("indexshortcut" 0)

    '("extendtheindex" 4) )

   ;; Add splitidx to the parser.
   (TeX-auto-add-regexp LaTeX-splitidx-newindex-regex)

   ;; Borrowed from index.el
   (add-to-list 'LaTeX-auto-regexp-list
		`(,(concat "\\\\sindex\\(?:\\[[^{}]*\\]\\)?"
			   "{\\([^}{]*\\({[^}{]*\\({[^}{]*\\({[^}{]*}[^}{]*\\)*"
			   "}[^}{]*\\)*}[^}{]*\\)*\\)}")
		  1 LaTeX-auto-index-entry))

   ;; Completion for \sindex entries
   (add-to-list 'TeX-complete-list
		'("\\\\sindex\\(\\[[^][{}]*\\]\\)?{\\([^{}\n\r]*\\)"
		  2 LaTeX-index-entry-list "}"))

   ;; Completion for the |see macro
   (add-to-list 'TeX-complete-list
		'("|see{\\([^{}\n\r]*\\)" 1 LaTeX-index-entry-list))

   ;; Tell RefTeX with `reftex-add-index-macros'
   (when (fboundp 'reftex-add-index-macros)
     (reftex-add-index-macros
      `(("\\sindex[]{*}" 1 ,LaTeX-splitidx-sindex-reftex-quick-id-key "" nil t))))

   ;; 3.2 Marking up index entries
   ;; \index should be an alias for \sindex
   (when (LaTeX-provided-package-options-member "splitidx" "useindex")
       (TeX-add-symbols
	'("index"
	  [TeX-arg-eval completing-read
			(TeX-argument-prompt optional nil "Short cut")
			(LaTeX-splitidx-newindex-list) ]
	  (TeX-arg-index)))
       ;; Tell RefTeX to look in the optional arg. for the index short cut
       (when (fboundp 'reftex-add-index-macros)
	 (reftex-add-index-macros '(("\\index[]{*}" 1 ?i "" nil t))))
       (add-to-list 'LaTeX-auto-regexp-list
		    `(,(concat
			"\\\\index\\(?:\\[[^{}]*\\]\\)?"
			"{\\([^}{]*\\({[^}{]*\\({[^}{]*\\({[^}{]*}[^}{]*\\)*"
			"}[^}{]*\\)*}[^}{]*\\)*\\)}")
		      1 LaTeX-auto-index-entry))
       (when (and (featurep 'font-latex)
		  (eq TeX-install-font-lock 'font-latex-setup))
	 (font-latex-add-keywords '(("index" "[{"))
				  'reference)))

   ;; 3.5 Automatic custom index commands
   ;; With package option `idxcommands', one can write \foo{<entry>}
   ;; instead of \sindex[foo]{<entry>}
   (when (and (LaTeX-provided-package-options-member "splitidx" "idxcommands")
	      (LaTeX-splitidx-newindex-list))
     (dolist (elt (mapcar #'car (LaTeX-splitidx-newindex-list)))
       ;; Make every `foo' available as a command
       (TeX-add-symbols `(,elt TeX-arg-index))
       ;; Add new macros's to `ispell-tex-skip-alist': skip one argument
       (TeX-ispell-skip-setcar `((,elt ispell-tex-arg-end)))
       ;; Cater for font-locking
       (when (and (featurep 'font-latex)
		  (eq TeX-install-font-lock 'font-latex-setup))
	 (font-latex-add-keywords `((,elt  "{"))
				  'reference))
       ;; Add defined <entry> to `LaTeX-index-entry-list'
       (add-to-list 'LaTeX-auto-regexp-list
		    `(,(concat
			"\\\\"
			elt
			"{\\([^}{]*\\({[^}{]*\\({[^}{]*\\({[^}{]*}[^}{]*\\)*"
			"}[^}{]*\\)*}[^}{]*\\)*\\)}")
		      1 LaTeX-auto-index-entry)) ))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("newindex"           "[{")
				("AtWriteToIndex"     "{{")
				("AtNextWriteToIndex" "{{")
				("newprotectedindex"  "[{")
				("setindexpreamble"   "[{")
				("useindexpreamble"   "[")
				("extendtheindex"     "{{{{"))
			      'function)
     (font-latex-add-keywords '(("sindex"             "[{"))
			      'reference)))
 LaTeX-dialect)

(defvar LaTeX-splitidx-package-options
  '("makeindex"
    "useindex"
    "allintoone"
    "split"
    "protected"
    "idxcommands")
  "Prompt for package options for the splitidx package.")

;;; splitidx.el ends here
