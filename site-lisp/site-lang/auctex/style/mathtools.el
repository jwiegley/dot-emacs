;;; mathtools.el --- Style hook for the LaTeX package `mathtools'.

;; Copyright (C) 2011-2012, 2014, 2016 Free Software Foundation, Inc.

;; Author: Mads Jensen <mje@inducks.org>
;; Created: 2011-02-13
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

;;  This file adds support for `mathtools.sty'

;;; Comments:

;;; This package serves as a wrapper for amsmath, adding more features
;;; and fixing a few bugs in amsmath.  The mathstyle argument for many
;;; of the macros is discussed at
;;; <http://www.tug.org/TUGboat/Articles/tb22-4/tb72perlS.pdf>

;;; Code:

;; Needed for auto-parsing.
(require 'tex)

;; amsmath options which can be passed directly to mathtools are
;; appended in the style hook below
(defvar LaTeX-mathtools-package-options
  '("fixamsmath" "donotfixamsmathbugs" "allowspaces" "disallowspaces"
    ;; Update 2013: We now make \(\) and \[\] robust (can be disabled
    ;; via nonrobust package option)
    "nonrobust")
  "Package options for the mathtools package.")

(defvar LaTeX-mathtools-key-val-options
  '(("showonlyrefs")
    ("mathic" ("true" "false"))
    ("showmanualtags" ("true" "false"))
    ;; 3.4.1 Matrices
    ("smallmatrix-align" ("c" "l" "r"))
    ("smallmatrix-inner-space")
    ;; 3.4.2 The multlined environment
    ("firstline-afterskip")
    ("lastline-preskip")
    ("multlined-pos" ("c" "b" "t"))
    ("multlined-width")
    ;; 3.4.7 Centered \vdots
    ("shortvdotsadjustabove")
    ("shortvdotsadjustbelow")
    ;; 3.5 Intertext and short intertext
    ("original-intertext" ("true" "false"))
    ("original-shortintertext" ("true" "false"))
    ("above-intertext-sep")
    ("below-intertext-sep")
    ("above-shortintertext-sep")
    ("below-shortintertext-sep")
    ;; 3.7.2 Vertically centered colon
    ("centercolon" ("true" "false"))
    ;; 4.2 Left sub/superscripts
    ("prescript-sub-format")
    ("prescript-sup-format")
    ("prescript-arg-format"))
  "Options for the \\mathtoolsset command.")

;; Setup for \newtagform
(TeX-auto-add-type "mathtools-newtagform" "LaTeX")

(defvar LaTeX-mathtools-newtagform-regexp
  '("\\\\newtagform{\\([^}]+\\)}"
    1 LaTeX-auto-mathtools-newtagform)
  "Matches the first argument of \\newtagform from mathtools package.")

;; Setup for \DeclarePairedDelimiter(X)?:
(TeX-auto-add-type "mathtools-DeclarePairedDelimiter" "LaTeX")

(defvar LaTeX-mathtools-DeclarePairedDelimiter-regexp
  `(,(concat "\\\\DeclarePairedDelimiter\\(?:X\\|XPP\\)?"
	     "{?"
	     "\\\\\\([a-zA-Z]+\\)"
	     "}?"
	     "\\(?:\\[\\([0-9]+\\)\\]\\)?")
    (1 2) LaTeX-auto-mathtools-DeclarePairedDelimiter)
  "Match the arguments of \\DeclarePairedDelimiterX? from mathtools package.")

;; Setup for \newgathered
(TeX-auto-add-type "mathtools-newgathered" "LaTeX")

(defvar LaTeX-mathtools-newgathered-regexp
  '("\\\\newgathered{\\([^}]+\\)}"
    1 LaTeX-auto-mathtools-newgathered)
  "Matches the first argument of \\newgathered from mathtools package.")

(defun LaTeX-mathtools-auto-prepare ()
  "Clear various variables for mathtools package before parsing."
  (setq LaTeX-auto-mathtools-newtagform             nil
	LaTeX-auto-mathtools-DeclarePairedDelimiter nil
	LaTeX-auto-mathtools-newgathered            nil))

(defun LaTeX-mathtools-auto-cleanup ()
  "Process the parsed elements for mathtools package."
  (when (LaTeX-mathtools-DeclarePairedDelimiter-list)
    (dolist (delim (LaTeX-mathtools-DeclarePairedDelimiter-list))
      (let ((cmd (car delim))
	    (arg (cadr delim)))
	(TeX-add-symbols `(,cmd [ LaTeX-mathtools-arg-mathsize-completion ]
				,(if (string= arg "")
				     1
				   (string-to-number arg)))
			 `(,(concat cmd "*")
			   ,(if (string= arg "")
				1
			      (string-to-number arg)))))))
  (when (LaTeX-mathtools-newgathered-list)
    (dolist (env (mapcar #'car (LaTeX-mathtools-newgathered-list)))
      (LaTeX-add-environments env)
      (add-to-list 'LaTeX-item-list
		   `(,env . LaTeX-item-equation) t)
      (add-to-list 'LaTeX-label-alist
		   `(,env . LaTeX-amsmath-label) t)
      (when (fboundp 'reftex-add-label-environments)
	(reftex-add-label-environments `((,env ?e nil nil t)))))))

(add-hook 'TeX-auto-prepare-hook #'LaTeX-mathtools-auto-prepare t)
(add-hook 'TeX-auto-cleanup-hook #'LaTeX-mathtools-auto-cleanup t)
(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)

(defun LaTeX-mathtools-arg-mathstyle-completion (optional)
  "Query and insert mathstyle argument to various commands.
If OPTIONAL, insert it as optional argument in brackets."
  (TeX-argument-insert
   (completing-read
    (TeX-argument-prompt optional nil
			 (concat "Math style: " TeX-esc) t)
    '("displaystyle" "textstyle"
      "scriptstyle"  "scriptscriptstyle"))
   optional TeX-esc))

(defun LaTeX-mathtools-arg-mathsize-completion (optional)
  "Query and insert math size argument to various commands.
If OPTIONAL, insert it as optional argument in brackets."
  (TeX-argument-insert
   (completing-read
    (TeX-argument-prompt optional nil
			 (concat "Size command: " TeX-esc) t)
    '("big" "Big" "bigg" "Bigg"))
   optional TeX-esc))

(defun LaTeX-mathtools-arg-declarepaireddelimiter (optional &optional X)
  "Query and insert various \\DeclarePairedDelimiter macros from mathtools package."
  (let ((cmd (TeX-read-string (concat "Command: " TeX-esc)))
	(arg (when X (TeX-read-string
		      (TeX-argument-prompt t nil "Number of arguments")))))
    (TeX-add-symbols `(,cmd [ LaTeX-mathtools-arg-mathsize-completion ]
			    ,(if X
				 ;; This is no precaution, arg has to be > 0
				 (string-to-number arg)
			       1))
		     `(,(concat cmd "*")
		       ,(if X
			    (string-to-number arg)
			  1)))
    (LaTeX-add-mathtools-DeclarePairedDelimiters
     `(,cmd ,(if X arg "")))
    (TeX-argument-insert cmd optional TeX-esc)
    (when arg
      (insert (concat LaTeX-optop arg LaTeX-optcl)))))

(defun LaTeX-mathtools-env-multlined (env)
  "Query and insert two optional arguments for ENV multlined.
If both arguments are given, insert them in brackets.  If only a
width is given, insert it prefixed with a pair of empty
brackets."
  (let ((pos (TeX-read-string
	      (TeX-argument-prompt t nil "Position (t, b or c (default))")))
	(width (completing-read
		(TeX-argument-prompt t nil "Width")
		(mapcar
		 (lambda (x) (concat TeX-esc (car x)))
		 (LaTeX-length-list)))))
    (LaTeX-insert-environment
     env
     (cond (;; both arguments
	    (and pos   (not (string= pos ""))
		 width (not (string= width "")))
	    (format "[%s][%s]" pos width))
	   (;; pos not empty, width empty
	    (and pos (not (string= pos ""))
		 (string= width ""))
	    (format "[%s]" pos))
	   (;; pos empty, width not
	    (and (string= pos "")
		 width (not (string= width "")))
	    (format "[][%s]" width))
	   (t nil)))))

(defun LaTeX-mathtools-env-cases (env)
  "Insert various cases ENVs incl. an ampersand from mathtools package."
  (LaTeX-insert-environment env)
  (save-excursion
    (insert ?&)))

(defun LaTeX-mathtools-item-cases ()
  "Insert contents to terminate a line in multi-line cases environment.
Put line break macro on the last line.  Next, insert an ampersand."
  (end-of-line 0)
  (just-one-space)
  (TeX-insert-macro "\\")
  (forward-line 1)
  (save-excursion
    (insert ?&)))

(TeX-add-style-hook
 "mathtools"
 (lambda ()

   ;; Add mathtools to parser
   (TeX-auto-add-regexp LaTeX-mathtools-newtagform-regexp)
   (TeX-auto-add-regexp LaTeX-mathtools-DeclarePairedDelimiter-regexp)
   (TeX-auto-add-regexp LaTeX-mathtools-newgathered-regexp)

   ;; "default" is pre-defined
   (LaTeX-add-mathtools-newtagforms "default")

   ;; mathtools requires amsmath, as some bugs in amsmath are fixed
   (TeX-run-style-hooks "amsmath")

   (dolist (elt LaTeX-amsmath-package-options)
     (add-to-list 'LaTeX-mathtools-package-options elt))

   (LaTeX-add-environments
    ;; 3.4.1 Matrices
    '("matrix*"  [ "Vertical alignment (l, r or c (default))" ])
    '("pmatrix*" [ "Vertical alignment (l, r or c (default))" ])
    '("bmatrix*" [ "Vertical alignment (l, r or c (default))" ])
    '("Bmatrix*" [ "Vertical alignment (l, r or c (default))" ])
    '("vmatrix*" [ "Vertical alignment (l, r or c (default))" ])
    '("Vmatrix*" [ "Vertical alignment (l, r or c (default))" ])
    '("smallmatrix*" [ "Vertical alignment (l, r or c (default))" ])
    '("psmallmatrix")
    '("psmallmatrix*" [ "Vertical alignment (l, r or c (default))" ])
    '("bsmallmatrix")
    '("bsmallmatrix*" [ "Vertical alignment (l, r or c (default))" ])
    '("Bsmallmatrix")
    '("Bsmallmatrix*" [ "Vertical alignment (l, r or c (default))" ])
    '("vsmallmatrix")
    '("vsmallmatrix*" [ "Vertical alignment (l, r or c (default))" ])
    '("Vsmallmatrix")
    '("Vsmallmatrix*" [ "Vertical alignment (l, r or c (default))" ])
    ;; 3.4.2 The multlined environment
    '("multlined" LaTeX-mathtools-env-multlined)
    ;; 3.4.3 More cases -like environments
    '("dcases"   LaTeX-mathtools-env-cases)
    '("dcases*"  LaTeX-mathtools-env-cases)
    '("rcases"   LaTeX-mathtools-env-cases)
    '("rcases*"  LaTeX-mathtools-env-cases)
    '("drcases"  LaTeX-mathtools-env-cases)
    '("drcases*" LaTeX-mathtools-env-cases)
    '("cases*"   LaTeX-mathtools-env-cases)
    ;; 4.4 Spreading equations
    '("spreadlines" "Spacing between lines")
    ;; 4.5 Gathered environments
    '("lgathered" ["Vertical position (t or b)"])
    '("rgathered" ["Vertical position (t or b)"]))

   (TeX-add-symbols
    '("mathtoolsset" (TeX-arg-key-val LaTeX-mathtools-key-val-options))
    ;; 3.1.1 A complement to \smash, \llap, and \rlap
    '("mathllap" [ LaTeX-mathtools-arg-mathstyle-completion ] t)
    '("mathrlap" [ LaTeX-mathtools-arg-mathstyle-completion ] t)
    '("mathclap" [ LaTeX-mathtools-arg-mathstyle-completion ] t)
    '("mathmakebox" [ (TeX-arg-length "Width") ] [ "Position" ] 1)
    '("clap" 1)
    '("mathmbox" 1)
    ;; 3.1.2 Forcing a cramped style
    '("cramped" [ LaTeX-mathtools-arg-mathstyle-completion ] 1)
    '("crampedllap" [ LaTeX-mathtools-arg-mathstyle-completion ] t)
    '("crampedrlap" [ LaTeX-mathtools-arg-mathstyle-completion ] t)
    '("crampedclap" [ LaTeX-mathtools-arg-mathstyle-completion ] t)
    ;; 3.1.3 Smashing an operator
    '("smashoperator" [ "Position (l, r or lr (default)" ] 1)
    ;; 3.1.4 Adjusting the limits of operators
    '("adjustlimits" t (TeX-arg-literal "_") nil nil (TeX-arg-literal "_") nil)
    ;; 3.1.5 Swapping space above AMS display math environments
    '("SwapAboveDisplaySkip" 0)
    ;; 3.2.1 The appearance of tags
    '("newtagform"
      (TeX-arg-eval
       (lambda ()
	 (let ((newtag (TeX-read-string
			(TeX-argument-prompt nil nil "Name"))))
	   (LaTeX-add-mathtools-newtagforms newtag)
	   (format "%s" newtag))))
       [ "Inner format" ] "Left" "Right")
    '("renewtagform"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt nil nil "Name")
		    (LaTeX-mathtools-newtagform-list))
      [ "Inner format" ] "Left" "Right")
    '("usetagform"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt nil nil "Name")
		    (LaTeX-mathtools-newtagform-list)))
    ;; 3.2.2 Showing only referenced tags
    '("refeq" TeX-arg-ref)
    '("noeqref" TeX-arg-ref)
    ;; 3.3.1 Arrow-like symbols
    '("xleftrightarrow" ["Below"] "Above")
    '("xLeftarrow" ["Below"] "Above")
    '("xRightarrow" ["Below"] "Above")
    '("xLeftrightarrow" ["Below"] "Above")
    '("xhookleftarrow" ["Below"] "Above")
    '("xhookrightarrow" ["Below"] "Above")
    '("xmapsto" ["Below"] "Above")
    '("xrightharpoondown" ["Below"] "Above")
    '("xrightharpoonup" ["Below"] "Above")
    '("xleftharpoondown" ["Below"] "Above")
    '("xleftharpoonup" ["Below"] "Above")
    '("xrightleftharpoons" ["Below"] "Above")
    '("xleftrightharpoons" ["Below"] "Above")
    ;; 3.3.2 Braces and brackets
    '("underbracket" [ (TeX-arg-length "Rule thickness") ]
		     [ (TeX-arg-length "Bracket height") ] t)
    '("overbracket"  [ (TeX-arg-length "Rule thickness") ]
		     [ (TeX-arg-length "Bracket height") ] t)
    '("underbrace" 1)
    '("overbrace" 1)
    '("LaTeXunderbrace" 1)
    '("LaTeXoverbrace" 1)
    ;; 3.4.2
    '("shoveleft"  [ (TeX-arg-length "Dimension") ] 1)
    '("shoveright" [ (TeX-arg-length "Dimension") ] 1)
    ;; 3.4.4
    '("MoveEqLeft" [ "Number" ])
    ;; 3.4.5 Boxing a single line in an alignment
    '("Aboxed" 1)
    ;; 3.4.6 Adding arrows between lines in an alignment
    '("ArrowBetweenLines" [ TeX-arg-macro ] )
    '("ArrowBetweenLines*" [ TeX-arg-macro ] )
    ;; 3.4.7 Centered \vdots
    '("vdotswithin" "Symbol")
    '("shortvdotswithin" "Symbol")
    '("shortvdotswithin*" "Symbol")
    '("MTFlushSpaceAbove")
    '("MTFlushSpaceBelow")
    ;; 3.5 Intertext and short intertext
    ;; don't understand t, but intertext in amsmath.el uses it
    '("shortintertext" t)
    ;; 3.6 Paired delimiters
    '("DeclarePairedDelimiter"
      LaTeX-mathtools-arg-declarepaireddelimiter
      "Left delimiter" "Right delimiter")
    '("DeclarePairedDelimiterX"
      (LaTeX-mathtools-arg-declarepaireddelimiter t)
      "Left delimiter" "Right delimiter" t)
    '("DeclarePairedDelimiterXPP"
      (LaTeX-mathtools-arg-declarepaireddelimiter t)
      "Pre-code" "Left delimiter" "Right delimiter" 2)
    '("delimsize" 0)
    ;; 3.6.1 Expert use
    '("reDeclarePairedDelimiterInnerWrapper"
      (TeX-arg-eval
       (lambda ()
	 (let ((cmd (completing-read
		     (concat "Command: " TeX-esc)
		     (mapcar #'car (LaTeX-mathtools-DeclarePairedDelimiter-list)))))
	   (concat TeX-esc cmd))))
      (TeX-arg-eval completing-read
		    "star or nostar: "
		    '("star" "nostar"))
      t)
    ;; 3.7.1 Left and right parentheses
    '("lparen" TeX-arg-insert-right-brace-maybe)
    '("rparen")
    ;; 3.7.2 Vertically centered colon
    "vcentcolon" "ordinarycolon" "coloneqq" "Coloneqq"
    "coloneq" "Coloneq" "eqqcolon" "Eqqcolon" "eqcolon"
    "Eqcolon" "colonapprox" "Colonapprox" "colonsim" "Colonsim"
    "dblcolon"
    ;; 3.7.3 A few missing symbols
    "nuparrow" "ndownarrow" "bigtimes"
    ;; 4.2 Left sub/superscripts
    '("prescript" "Below" "Above" t)
    ;; 4.3 Declaring math sizes
    '("DeclareMathSizes" 4)
    ;; 4.5 Gathered environments
    '("newgathered"
      (TeX-arg-eval
       (lambda ()
	 (let ((env (TeX-read-string
		     (TeX-argument-prompt nil nil "Name"))))
	   (LaTeX-add-environments env)
	   (LaTeX-add-mathtools-newgathereds env)
	   (add-to-list 'LaTeX-item-list
			`(,env . LaTeX-item-equation) t)
	   (add-to-list 'LaTeX-label-alist
			`(,env . LaTeX-amsmath-label) t)
	   (format "%s" env))))
      3)
    '("renewgathered"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt nil nil "Name")
		    (LaTeX-mathtools-newgathered-list))
      3)
    ;; 4.6 Split fractions
    '("splitfrac" 2)
    '("splitdfrac" 2))

   ;; Append delimiters to `TeX-braces-association'
   ;; 3.7.1 Left and right parentheses
   (make-local-variable 'TeX-braces-association)
   (add-to-list 'TeX-braces-association '("\\lparen" . "\\rparen") t)

   (setq LaTeX-item-list
	 (append '(("multlined"   . LaTeX-item-equation)
		   ("lgathered"   . LaTeX-item-equation)
		   ("rgathered"   . LaTeX-item-equation)
		   ("spreadlines" . LaTeX-item-equation)
		   ("matrix*"     . LaTeX-item-equation)
		   ("pmatrix*"    . LaTeX-item-equation)
		   ("bmatrix*"    . LaTeX-item-equation)
		   ("Bmatrix*"    . LaTeX-item-equation)
		   ("vmatrix*"    . LaTeX-item-equation)
		   ("Vmatrix*"    . LaTeX-item-equation)
		   ("dcases"      . LaTeX-mathtools-item-cases)
		   ("dcases*"     . LaTeX-mathtools-item-cases)
		   ("rcases"      . LaTeX-mathtools-item-cases)
		   ("rcases*"     . LaTeX-mathtools-item-cases)
		   ("drcases"     . LaTeX-mathtools-item-cases)
		   ("drcases*"    . LaTeX-mathtools-item-cases)
		   ("cases*"      . LaTeX-mathtools-item-cases))
		 LaTeX-item-list))

   (setq LaTeX-label-alist
	 (append '(("lgathered" . LaTeX-amsmath-label)
		   ("rgathered" . LaTeX-amsmath-label)
		   ("multlined" . LaTeX-amsmath-label))
		 LaTeX-label-alist))

   ;; RefTeX support: Add env's with `reftex-add-label-environments'
   (when (fboundp 'reftex-add-label-environments)
     (let ((envs '(("lgathered"  ?e nil nil t)
		   ("rgathered"  ?e nil nil t)
		   ("multlined"  ?e nil nil t))))
       (dolist (env envs)
	 (reftex-add-label-environments `(,env)))))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("mathtoolsset"  "{")
				("newtagform"    "{[{{")
				("renewtagform"  "{[{{")
				("DeclarePairedDelimiter"     "|{\\{{")
				("DeclarePairedDelimiterX"    "|{\\[{{{")
				("DeclarePairedDelimiterXPP"  "|{\\[{{{{{")
				("reDeclarePairedDelimiterInnerWrapper" "|{\\{{")
				("DeclareMathSizes"           "{{{{")
				("newgathered"                "{{{{")
				("renewgathered"              "{{{{"))
			      'function)
     (font-latex-add-keywords '(("usetagform" "{"))
			      'variable)
     (font-latex-add-keywords '(("refeq"   "{")
				("noeqref" "{"))
			      'reference)))
 LaTeX-dialect)

;;; mathtools.el ends here
