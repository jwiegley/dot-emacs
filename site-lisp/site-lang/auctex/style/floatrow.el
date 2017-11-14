;;; floatrow.el --- AUCTeX style for `floatrow.sty' (v0.3b)

;; Copyright (C) 2017 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2016-11-11
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

;; This file adds support for `floatrow.sty' (v0.3b) from 2009/08/02.
;; `floatrow.sty' is part of TeXLive.
;;
;; `floatrow.sty' is a powerful package and the documentation long.
;; It is expected that this style is not feature complete.  One
;; deliberate decision is that this style does not offer any package
;; options: Please use the command `\floatsetup' to set the options
;; you want.
;;
;; This style also alters the way AUCTeX inserts the environments
;; "table" and "figure" (cf.  function `LaTeX-floatrow-env-init').  If
;; you want the original behavior, try `C-c C-e rawfigure' or `C-c C-e
;; rawtable' which include the environments incl.  the macro \RawFloats
;; at the beginning of the environment (cf.  function
;; `LaTeX-floatrow-env-figure-raw').
;;
;; Another deliberate decision is the implementation of commands like
;; `\ffigbox' and `\ttabbox': When invoked with `C-c C-m ffigbox RET',
;; the final result will look like this with cursor being at *:
;;
;;   \ffigbox{*}{%
;;     \caption{query for a caption}%
;;     \label{prefix:is-chosen-acc-to-current-environment}%
;;   }
;;
;; This gives users the freedom to insert any command where point is.
;; The mandatory arguments are not part of the fontification as
;; commands like `\includegraphics' or `tabular' environments have their
;; own fontification.

;;; Code:

;; Needed for compiling `pushnew':
(eval-when-compile (require 'cl))

;; Needed for auto-parsing.
(require 'tex)

(defvar LaTeX-floatrow-key-val-options
  '(;; 3.1.1 Float Style
    ("style" ("plain" "plaintop" "Plaintop"
	      "ruled" "Ruled"
	      "boxed" "Boxed" "BOXED"
	      "shadowbox" "Shadowbox" "SHADOWBOX"
	      "doublebox" "Doublebox" "DOUBLEBOX"
	      "wshadowbox" "Wshadowbox" "WSHADOWBOX"))
    ;; 3.1.2 Font Settings
    ("font" ("scriptsize" "footnotesize" "small" "normalsize" "large"
	     "Large" "normalfont" "up" "it" "sl" "sc" "md" "bf"
	     "rm" "sf" "tt"))
    ("footfont" ("scriptsize" "footnotesize" "small" "normalsize" "large"
		 "Large" "normalfont" "up" "it" "sl" "sc" "md" "bf"
		 "rm" "sf" "tt"))
    ;; 3.1.3 Position of Caption
    ("capposition" ("top" "TOP" "bottom" "beside"))
    ;; 3.1.4 Position of Beside Caption
    ("capbesideposition" ("left" "right" "inside" "outside"
			  "top" "bottom" "center"))
    ;; 3.1.5 Defining The Width of Beside Caption
    ("capbesidewidth" ("none" "sidefil"))
    ;; 3.1.6 Defining Width of Object
    ("floatwidth" ("\\hsize" "\\textwidth" "\\columnwidth" "\\linewidth"))
    ;; 3.1.7 Other Settings for Beside Captions
    ("capbesideframe" ("yes" "no"))
    ;; 3.1.8 Defining Float Foot Position (Legends and Footnotes)
    ("footposition" ("default" "caption" "bottom"))
    ;; 3.1.9 Vertical Alignment of Float Elements
    ("heightadjust" ("all" "caption" "object" "none" "nocaption" "noobject"))
    ("valign" ("t" "c" "b" "s"))
    ;; 3.1.10 Facing Layout
    ("facing" ("yes" "no"))
    ;; 3.1.11 Object Settings
    ("objectset" ("justified" "centering" "raggedright" "RaggedRight" "raggedleft"))
    ;; 3.1.12 Defining Float Margins
    ("margins" ("centering" "raggedright" "raggedleft"
		"hangright" "hanginside" "hangoutside"))
    ;; 3.1.13 Defining Float Separators
    ("floatrowsep" ("columnsep" "quad" "qquad" "hfil" "hfill" "none"))
    ("capbesidesep" ("columnsep" "quad" "qquad" "hfil" "hfill" "none"))
    ;; 3.1.14 Defining Float Rules/Skips
    ("precode" ("none" "thickrule" "rule" "lowrule" "captionskip"))
    ("rowprecode" ("none" "thickrule" "rule" "lowrule" "captionskip"))
    ("midcode" ("none" "thickrule" "rule" "lowrule" "captionskip"))
    ("postcode" ("none" "thickrule" "rule" "lowrule" "captionskip"))
    ("rowpostcode" ("none" "thickrule" "rule" "lowrule" "captionskip"))
    ;; 3.1.15 Defining Float Frames
    ("framestyle" ("fbox" "colorbox" "FRcolorbox" "corners"
		   "doublebox" "shadowbox" "wshadowbox"))
    ("frameset")
    ("framearound" ("none" "object" "all" "row" "none"))
    ("framefit" ("yes" "no"))
    ("rowfill" ("yes" "no"))
    ;; 3.1.16 Settings for Colored Frames
    ("colorframeset")
    ("colorframecorners")
    ;; 3.1.17 Defining Float Skips
    ("captionskip")
    ("footskip")
    ;; 3.1.18 Defining Float Footnote Rule's Style
    ("footnoterule" ("normal" "limited" "fullsize" "none"))
    ;; 3.1.19 Managing Floats with [H] Placement Option
    ("doublefloataswide" ("yes" "no"))
    ("floatHaslist" ("yes" "no"))
    ;; 7.2.1 Additions in The floatrow Package to longtable package
    ("LTcapwidth" ("table" "contents")))
  "Key=value options for floatrow macros and environments.")

(defvar LaTeX-floatrow-key-val-options-local nil
  "Buffer-local key=value options for floatrow macros and environments.")
(make-variable-buffer-local 'LaTeX-floatrow-key-val-options-local)

(defvar LaTeX-floatrow-supported-float-types
  '("figure" "table"				  ; Standard LaTeX
    "widefigure" "widetable" "widefloat"	  ; Standard figure* & table*
    "wrapfigure" "wraptable" "wrapfloat"	  ; wrapfig.sty
    "rotfigure"  "rottable"  "rotfloat"           ; rotating.sty
    "widerotfigure" "widerottable" "widerotfloat" ; for 2-col & wide
    "figurerow"  "tablerow"  "floatrow"           ; inside floatrow env's
    "capbesidefigure" "capbesidetable"            ; floats with beside captions
    "capbesidefloat"
    "longtable"					  ; longtable.sty
    "subfigure" "subtable" "sub")                 ; subcaption.sty
  "List of float types supported by floatrow.sty.")

;; Setup for \newfloatcommand
(TeX-auto-add-type "floatrow-newfloatcommand" "LaTeX")

(defvar LaTeX-floatrow-newfloatcommand-regexp
  '("\\\\newfloatcommand{\\([^}]+\\)}" 1 LaTeX-auto-floatrow-newfloatcommand)
  "Matches the arguments of \"\\newfloatcommand\" from floatrow.sty.")

;; Setup for various \Declare* macros:
(TeX-auto-add-type "floatrow-DeclareNewOption" "LaTeX")

(defvar LaTeX-floatrow-DeclareNewOption-regexp
  `(,(concat
      "\\\\Declare"
      "\\("
      (mapconcat #'identity
		 '("FloatStyle"         ; 3.6.1 Float Style Option (style=)
		   "FloatFont"          ; 3.6.2 Float Font Option (font=)
		   "FloatVCode"         ; 3.6.3 Option for Float Rules/Skips (precode= etc.)
		   "ColorBox"           ; 3.6.4 Settings for Colored Frame (colorframeset=)
		   "CBoxCorners"        ;       colorframecorners=
		   "ObjectSet"          ; 3.6.5 Object Justification Option (objectset=)
		   "MarginSet"          ; 3.6.6 Option for Float Box Alignment/Settings (margins=)
		   "FloatSeparators"    ; 3.6.7 Float Separators Options (floatrowsep=, capbesidesep=)
		   "FloatFootnoterule") ; 3.6.8 Option for Footnote Rule's Style (footnoterule=)
		 "\\|")
      "\\)"
      "{\\([^}]+\\)}")
    (0 1 2) LaTeX-auto-floatrow-DeclareNewOption)
  "Matches the arguments of \"\\Declare*\" from floatrow.sty.")

;; Setup for \newseparated(label|ref):
(TeX-auto-add-type "floatrow-newseparatedlabel-ref" "LaTeX")

(defvar LaTeX-floatrow-newseparatedlabel-ref-regexp
  `(,(concat
      "\\\\newseparated"
      "\\(label\\|ref\\)"
      "{?"
      "\\\\"
      "\\([a-zA-Z]+\\)"
      "}?")
    (2 1) LaTeX-auto-floatrow-newseparatedlabel-ref)
  "Matches the arguments \"\\newseparated(label|ref)\" command from floatrow.sty.")

;; Setup for \DeclareNewFloatType:
(TeX-auto-add-type "floatrow-DeclareNewFloatType" "LaTeX")

(defvar LaTeX-floatrow-DeclareNewFloatType-regexp
  '("\\\\DeclareNewFloatType{\\([^}]+\\)}"
    1 LaTeX-auto-floatrow-DeclareNewFloatType)
  "Matches the argument of \"\\DeclareNewFloatType\" command from floatrow.sty.")

;; Plug them into the machinery.
(defun LaTeX-floatrow-auto-prepare ()
  "Clear various \"LaTeX-floatrow\" variables before parsing."
  (setq LaTeX-auto-floatrow-newfloatcommand       nil
	LaTeX-auto-floatrow-DeclareNewOption      nil
	LaTeX-auto-floatrow-newseparatedlabel-ref nil
	LaTeX-auto-floatrow-DeclareNewFloatType   nil))

(defun LaTeX-floatrow-auto-cleanup ()
  "Process parsed results from floatrow package."
  ;; Replace initially the way fig & tab env's are inserted:
  (LaTeX-floatrow-env-init)
  ;;
  ;; Process new key=val options:
  (when (LaTeX-floatrow-DeclareNewOption-list)
    (LaTeX-floatrow-update-key-val-options))
  ;;
  ;; Process new float commands like \ffigbox:
  (when (LaTeX-floatrow-newfloatcommand-list)
    (dolist (cmd (mapcar #'car (LaTeX-floatrow-newfloatcommand-list)))
      (TeX-add-symbols `(,cmd LaTeX-floatrow-arg-floatbox))
      (when (and (featurep 'font-latex)
		 (eq TeX-install-font-lock 'font-latex-setup))
	(font-latex-add-keywords `((,cmd "[[["))
				 'textual))))
  ;;
  ;; Process new label/ref commands:
  (when (LaTeX-floatrow-newseparatedlabel-ref-list)
    (let (floatrow-run-reftex-compile-vars)
      (dolist (elt (LaTeX-floatrow-newseparatedlabel-ref-list))
	(let ((cmd (car elt))
	      (type (cadr elt)))
	  (if (string= type "ref")
	      ;; More fun w/ referencing macros:
	      (TeX-add-symbols `(,cmd TeX-arg-ref))
	    ;; Less fun w/ label defining macros.  Add cmd to
	    ;; TeX-symbol-list:
	    (TeX-add-symbols `(,cmd TeX-arg-define-label))
	    ;; For AUCTeX, parse the argument of the new macro and add
	    ;; it to `LaTeX-auto-label':
	    (TeX-auto-add-regexp
	     `(,(concat "\\\\" cmd "{\\([^\n\r%\\{}]+\\)}") 1 LaTeX-auto-label))
	    ;; For RefTeX, append cmd to `reftex-label-regexps and set
	    ;; floatrow-run-reftex-compile-vars to t:
	    (when (and (boundp 'reftex-label-regexps)
		       (fboundp 'reftex-compile-variables)
		       (not (string-match
			     cmd
			     (mapconcat #'identity reftex-label-regexps "|"))))
	      (add-to-list (make-local-variable 'reftex-label-regexps)
			   (concat "\\\\" cmd "{\\(?1:[^}]*\\)}") t)
	      (setq floatrow-run-reftex-compile-vars t)))
	  ;; Fontify macros as reference:
	  (when (and (featurep 'font-latex)
		     (eq TeX-install-font-lock 'font-latex-setup))
	    (font-latex-add-keywords `((,cmd "{"))
				     'reference))))
      ;; Run `reftex-compile-variables' if needed only once:
      (when floatrow-run-reftex-compile-vars
	(reftex-compile-variables))))
  ;;
  ;; Process new floattypes:
  (when (LaTeX-floatrow-DeclareNewFloatType-list)
    (LaTeX-floatrow-arg-declare-new-floattype nil t))
  ;;
  ;; Add elements from `LaTeX-floatrow-supported-float-types' to
  ;; `LaTeX-caption-supported-float-types':
  (when (boundp 'LaTeX-caption-supported-float-types)
    (make-local-variable 'LaTeX-caption-supported-float-types)
    (dolist (float LaTeX-floatrow-supported-float-types)
      (add-to-list 'LaTeX-caption-supported-float-types float t))) )

(add-hook 'TeX-auto-prepare-hook #'LaTeX-floatrow-auto-prepare t)
(add-hook 'TeX-auto-cleanup-hook #'LaTeX-floatrow-auto-cleanup t)
(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)

(defun LaTeX-floatrow-update-key-val-options ()
  "Update buffer-local key-val options before offering for completion."
  (let ((vcode-keys '("precode" "rowprecode" "midcode" "postcode" "rowpostcode"))
	(sep-keys '("floatrowsep" "capbesidesep")))
    (dolist (keyvals (LaTeX-floatrow-DeclareNewOption-list))
      (let* ((key (cond ((string= (nth 1 keyvals) "FloatStyle")
			 "style")
			((string= (nth 1 keyvals) "FloatFont")
			 "font")
			((string= (nth 1 keyvals) "FloatVCode")
			 "precode")
			((string= (nth 1 keyvals) "ColorBox")
			 "colorframeset")
			((string= (nth 1 keyvals) "CBoxCorners")
			 "colorframecorners")
			((string= (nth 1 keyvals) "ObjectSet")
			 "objectset")
			((string= (nth 1 keyvals) "MarginSet")
			 "margins")
			((string= (nth 1 keyvals) "FloatSeparators")
			 "floatrowsep")
			((string= (nth 1 keyvals) "FloatFootnoterule")
			 "footnoterule")
			(t nil)))
	     (val (nth 2 keyvals))
	     (val-match (cadr (assoc key LaTeX-floatrow-key-val-options-local)))
	     (temp (copy-alist LaTeX-floatrow-key-val-options-local))
	     (opts (cond ((string= key "precode")
			  (dolist (x vcode-keys)
			    (setq temp (assq-delete-all (car (assoc x temp)) temp)))
			  temp)
			 ((string= key "floatrowsep")
			  (setq temp (dolist (x sep-keys)
				       (assq-delete-all (car (assoc x temp)) temp)))
			  temp)
			 (t
			  (assq-delete-all (car (assoc key temp)) temp)))))
	(cond ((string= key "precode")
	       (dolist (x vcode-keys)
		 (pushnew (list x (delete-dups (append (list val) val-match)))
			  opts :test #'equal)))
	      ((string= key "floatrowsep")
	       (dolist (x sep-keys)
		 (pushnew (list x (delete-dups (append (list val) val-match)))
			  opts :test #'equal)))
	      (t
	       (pushnew (list key (delete-dups (append (list val) val-match)))
			opts :test #'equal)))
	(setq LaTeX-floatrow-key-val-options-local (copy-alist opts))))))

(defun LaTeX-floatrow-arg-floatbox (optional)
  "Query and insert arguments of float box commands from floatrow.sty.
If OPTIONAL is non-nil, indicate optional argument during query."
  ;; Query for the optional arguments; ask for "vertpos" only if
  ;; "height" is given.  let-bind `TeX-arg-*-brace' for
  ;; `TeX-argument-insert':
  (let* ((TeX-arg-opening-brace "[")
	 (TeX-arg-closing-brace "]")
	 (width (completing-read
		 (TeX-argument-prompt t nil "Width")
		 (mapcar (lambda (x) (concat TeX-esc (car x)))
			 (LaTeX-length-list))))
	 (height (completing-read
		  (TeX-argument-prompt t nil "Height")
		 (mapcar (lambda (x) (concat TeX-esc (car x)))
			 (LaTeX-length-list))))
	 (vertpos (if (string= height "")
		      ""
		    (completing-read
		     (TeX-argument-prompt t nil "Vertical alignment")
		     '("t" "c" "b" "s")))))
    (TeX-argument-insert width t)
    ;; Insert an extra pair of brackets if only `height' is given,
    ;; otherwise it will become `width'
    (when (and (string= width "")
	       height (not (string= height "")))
      (insert "[]"))
    (TeX-argument-insert height t)
    (TeX-argument-insert vertpos t))
  ;; Now query for the (short-)caption.  Also check for the
  ;; float-type; if we're inside (sub)?floatrow*?, then check for the
  ;; next outer environment:
  (let* ((currenv (if (string-match "floatrow\\*?\\_>" (LaTeX-current-environment))
		      (LaTeX-current-environment 2)
		    (LaTeX-current-environment)))
	 (caption (TeX-read-string
		   (TeX-argument-prompt optional nil "Caption")))
	 (short-caption
	  (when (>= (length caption) LaTeX-short-caption-prompt-length)
	    (TeX-read-string
	     (TeX-argument-prompt t nil "Short caption")))))
    (indent-according-to-mode)
    ;; The final result will look like this with * being point:
    ;;   \ffigbox{*}{%
    ;;     \caption{text}%
    ;;     \label{fig:foo}%
    ;;   }
    (insert TeX-grop)
    (save-excursion
      ;; We are inside the 1. mandatory arg: Save the pos & insert `}{':
      (insert TeX-grcl TeX-grop)
      (if (and caption (not (string= caption "")))
	  (progn
	    ;; If caption, move to EOL, delete any spaces and hide the line end
	    (end-of-line)
	    (delete-horizontal-space)
	    (insert "%")
	    ;; Add a newline and the caption
	    (newline-and-indent)
	    (insert (LaTeX-compose-caption-macro caption short-caption))
	    ;; If we have a caption, then we probably also want a
	    ;; label.  Hide EOL end and proceed to enter a label
	    (insert "%")
	    (newline-and-indent)
	    (when (LaTeX-label currenv 'environment)
	      ;; Move point to end of line and hide EOL
	      (end-of-line)
	      (delete-horizontal-space)
	      (insert "%")
	      (newline-and-indent))
	    ;; Now close the group
	    (insert TeX-grcl)
	    (indent-according-to-mode)
	    (end-of-line))
	;; Otherwise, only insert a }
	(insert TeX-grcl)))))

(defun LaTeX-floatrow-env-init ()
  "Replace AUCTeX entries in the variable `LaTeX-environment-list'.
After loading the style hook floatrow.el, delete the entries for
figure*? and table*? from variable `LaTeX-environment-list' and
replace them with the ones offered by the style.  Original
entries are available under \"rawfigure*?\" and \"rawtable*?\"."
  (LaTeX-environment-list)
  (dolist (env '("figure" "figure*" "table" "table*"))
	  (setq LaTeX-environment-list
		(assq-delete-all (car (assoc env LaTeX-environment-list))
				 LaTeX-environment-list))
	  (LaTeX-add-environments `(,env LaTeX-floatrow-env-figure)
				  `(,(concat "raw" env) LaTeX-floatrow-env-figure-raw))))

(defun LaTeX-floatrow-env-figure (environment)
  "Create floating ENVIRONMENT suitable for floatrow macros."
  (let ((float (and LaTeX-float
		    (TeX-read-string
		     (TeX-argument-prompt t nil "Float position")
		     LaTeX-float))))
    (LaTeX-insert-environment environment
			      (unless (zerop (length float))
				(concat LaTeX-optop float LaTeX-optcl)))))

(defun LaTeX-floatrow-env-figure-raw (env)
  "Create raw floating ENV with floatrow.sty.
Also insert the macro \"\\RawFloats\" when finished with user
queries."
  (let ((environment (TeX-replace-regexp-in-string "raw" "" env)))
    (LaTeX-env-figure environment)
    (save-excursion
      ;; `LaTeX-find-matching-begin' will not work for us as we don't
      ;; know how user answers queries from AUCTeX, hence we search
      ;; back for `environment':
      (re-search-backward (concat "\\\\begin{" environment "}") nil t)
      (end-of-line)
      (LaTeX-newline)
      (indent-according-to-mode)
      (insert TeX-esc "RawFloats"))))

(defun LaTeX-floatrow-arg-declare-new-options (optional prompt key)
  "Query and insert user-defined values to keys provided by floatrow.sty.
If OPTIONAL is non-nil, ask for an optional argument and insert
it in square brackets.  PROMPT replaces the standard one.  KEY is
a string and corresponds to first parsed element in
`LaTeX-floatrow-DeclareNewOption-regexp'."
  (let ((val (TeX-read-string
	      (TeX-argument-prompt optional prompt "New value option"))))
    (LaTeX-add-floatrow-DeclareNewOptions
     (list (concat TeX-esc "Declare" key TeX-grop val TeX-grcl)
	   key val))
    (LaTeX-floatrow-update-key-val-options)
    (TeX-argument-insert val optional)
    (TeX-argument-insert
     (TeX-read-key-val optional LaTeX-floatrow-key-val-options-local) optional)))

(defun LaTeX-floatrow-arg-newseparatedlabel/ref (optional type)
  "Query and insert user defined label and reference macros from floatrow.sty.
If OPTIONAL is non-nil, insert the argument in brackets.  TYPE is
the string \"label\" or \"ref\"."
  (let ((cmd (TeX-read-string
	      (if (string= type "label")
		  (TeX-argument-prompt optional nil "Label command: \\" t)
		(TeX-argument-prompt optional nil "Reference command: \\" t)))))
    (LaTeX-add-floatrow-newseparatedlabel-refs (list cmd type))
    (if (string= type "label")
	(TeX-add-symbols `(,cmd TeX-arg-define-label))
      (TeX-add-symbols `(,cmd TeX-arg-ref)))
    (TeX-argument-insert cmd optional TeX-esc)))

(defun LaTeX-floatrow-arg-declare-new-floattype (optional &optional cleanup)
  "Query and insert the first argument of \"DeclareNewFloatType\" macro from floatrow.sty.
If OPTIONAL is non-nil, insert the argument in brackets.  If
CLEANUP in non-nil, skip the query and insert process as we are
inside the function `LaTeX-floatrow-auto-cleanup' and process
only the parsed items."
  (let ((type (if cleanup
		  (mapcar #'car (LaTeX-floatrow-DeclareNewFloatType-list))
		(list (TeX-read-string
		       (TeX-argument-prompt optional nil "Environment type"))))))
    ;; If not inside `LaTeX-floatrow-auto-cleanup', add user input to
    ;; list of new floats and insert it
    (unless cleanup
      (LaTeX-add-floatrow-DeclareNewFloatTypes (car type))
      (TeX-argument-insert (car type) optional))
    ;; Make the next variables buffer local
    (make-local-variable 'LaTeX-floatrow-supported-float-types)
    (when (boundp 'LaTeX-caption-supported-float-types)
      (make-local-variable 'LaTeX-caption-supported-float-types))
    ;; Process new float type(s): a) add type to list of known
    ;; environments incl. "raw" version b) add different flavors of
    ;; type to `LaTeX-floatrow-supported-float-types' c) check if
    ;; `LaTeX-caption-supported-float-types' is bound and add
    ;; different flavors of type to it as well
    (dolist (elt type)
      (LaTeX-add-environments `(,elt LaTeX-floatrow-env-figure)
			      `(,(concat "raw" elt) LaTeX-floatrow-env-figure-raw))
      (add-to-list 'LaTeX-floatrow-supported-float-types elt t)
      (add-to-list 'LaTeX-floatrow-supported-float-types (concat "wide" elt) t)
      (add-to-list 'LaTeX-floatrow-supported-float-types (concat elt "row") t)
      (add-to-list 'LaTeX-floatrow-supported-float-types (concat "capbeside" elt) t)
      (when (boundp 'LaTeX-caption-supported-float-types)
	(add-to-list 'LaTeX-caption-supported-float-types elt t)
	(add-to-list 'LaTeX-caption-supported-float-types (concat "wide" elt) t)
	(add-to-list 'LaTeX-caption-supported-float-types (concat elt "row") t)
	(add-to-list 'LaTeX-caption-supported-float-types (concat "capbeside" elt) t)))))

(TeX-add-style-hook
 "floatrow"
 (lambda ()

   ;; Add floatrow to the parser
   (TeX-auto-add-regexp LaTeX-floatrow-DeclareNewOption-regexp)
   (TeX-auto-add-regexp LaTeX-floatrow-newfloatcommand-regexp)
   (TeX-auto-add-regexp LaTeX-floatrow-newseparatedlabel-ref-regexp)
   (TeX-auto-add-regexp LaTeX-floatrow-DeclareNewFloatType-regexp)

   ;; Activate the buffer-local version of key-vals
   (setq LaTeX-floatrow-key-val-options-local
	 (copy-alist LaTeX-floatrow-key-val-options))

   ;; Add pre-defined float commands:
   (LaTeX-add-floatrow-newfloatcommands
    "ffigbox" "fcapside" "ttabbox")

   ;; Macros
   (TeX-add-symbols
    ;; 2.1 The \floatbox Macro
    ;; \floatbox[<preamble>]{<captype>}[<width>][<height>][<vert pos>]{<caption>}{<object>}
    '("floatbox"
      [ TeX-arg-eval completing-read
		     (TeX-argument-prompt optional nil "Preamble")
		     '("\\capbeside" "\\nocapbeside" "\\captop") ]
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Float type")
		    LaTeX-floatrow-supported-float-types)
      LaTeX-floatrow-arg-floatbox)

    ;; 2.2 Creation of Personal Commands for Float Boxes
    '("newfloatcommand"
      (TeX-arg-eval
       (lambda ()
	 (let ((cmd (TeX-read-string
		     (TeX-argument-prompt optional nil "Command"))))
	   (LaTeX-add-floatrow-newfloatcommands cmd)
	   (TeX-add-symbols
	    `(,cmd LaTeX-floatrow-arg-floatbox))
	   (format "%s" cmd))))
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Float type")
		    '("figure" "table"))
      [ 2 ])

    '("renewfloatcommand"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Command")
		    (LaTeX-floatrow-newfloatcommand-list))
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Float type")
		    '("figure" "table"))
      [ 2 ])


    ;; 2.2.2 Predefined Float Box Commands
    '("ffigbox"
      LaTeX-floatrow-arg-floatbox)

    '("ttabbox"
      LaTeX-floatrow-arg-floatbox)

    '("fcapside"
      LaTeX-floatrow-arg-floatbox)

    ;; 2.3.1 Mixed Row
    '("CenterFloatBoxes" 0)
    '("TopFloatBoxes" 0)
    '("BottomFloatBoxes" 0)
    '("PlainFloatBoxes" 0)
    '("buildFBBOX" 2)

    ;; 3 Float Layout Settings
    '("floatsetup"
      [ TeX-arg-eval completing-read
		     (TeX-argument-prompt optional nil "Float type")
		     LaTeX-floatrow-supported-float-types ]
      (TeX-arg-key-val LaTeX-floatrow-key-val-options-local))

    ;; 3.2 Settings for Current Float Environment
    '("thisfloatsetup"
      (TeX-arg-key-val LaTeX-floatrow-key-val-options-local))

    ;; 3.3 Clearing of Settings for Current Float Type
    '("clearfloatsetup"
      (TeX-arg-eval completing-read
		     (TeX-argument-prompt optional nil "Float type")
		     LaTeX-floatrow-supported-float-types))

    ;; 3.4 Temporary Clearing of All Float Settings
    '("killfloatstyle" 0)

    ;; 3.6.1 Float Style Option (style=)
    '("DeclareFloatStyle"
      (LaTeX-floatrow-arg-declare-new-options "New style option"
					      "FloatStyle"))

    ;; 3.6.2 Float Font Option (font=)
    '("DeclareFloatFont"
      (LaTeX-floatrow-arg-declare-new-options "New font option"
					      "FloatFont"))

    ;; 3.6.3 Option for Float Rules/Skips (precode= etc.)
    '("DeclareFloatVCode"
      (LaTeX-floatrow-arg-declare-new-options "New rules/skip option"
					      "FloatVCode"))

    ;; 3.6.4 Settings for Colored Frame (colorframeset=)
    '("DeclareColorBox"
      (LaTeX-floatrow-arg-declare-new-options "New colored frame option"
					      "ColorBox"))

    ;; (colorframecorners=)
    '("DeclareCBoxCorners"
      (LaTeX-floatrow-arg-declare-new-options "New colored corner option"
					      "CBoxCorners"))

    ;; 3.6.5 Object Justification Option (objectset=)
    '("DeclareObjectSet"
      (LaTeX-floatrow-arg-declare-new-options "New object justification"
					      "ObjectSet"))

    ;; 3.6.6 Option for Float Box Alignment/Settings (margins=)
    '("DeclareMarginSet"
      (LaTeX-floatrow-arg-declare-new-options "New alignment option"
					      "MarginSet"))

    '("setfloatmargins" 2)
    '("setfloatmargins*" 2)
    '("floatfacing" 2)
    '("floatfacing*" 2)
    '("floatboxmargins" 2)
    '("floatrowmargins" 2)
    '("floatcapbesidemargins" 2)

    ;; 3.6.7 Float Separators Options (floatrowsep=, capbesidesep=)
    '("DeclareFloatSeparators"
      (LaTeX-floatrow-arg-declare-new-options "New separator option"
					      "FloatSeparators"))

    ;; 3.6.8 Option for Footnote Rule's Style (footnoterule=)
    '("DeclareFloatFootnoterule"
      (LaTeX-floatrow-arg-declare-new-options "New footnote rule option"
					      "FloatFootnoterule"))

    ;; 4 Creation of New Float Types
    '("DeclareNewFloatType"
      (LaTeX-floatrow-arg-declare-new-floattype)
      (TeX-arg-key-val (("placement" ("tbp" "t" "b" "p"))
			("name")
			("fileext")
			("within" ("chapter" "section" "subsection"))
			("relatedcapstyle" ("yes" "no")))))

    ;; 6.2 Support of The Label-Sublabel References
    '("newseparatedlabel"
      (LaTeX-floatrow-arg-newseparatedlabel/ref "label") 2)

    '("newseparatedref"
      (LaTeX-floatrow-arg-newseparatedlabel/ref "ref") t)

    '("makelabelseparator" t) ) ;; terminate TeX-add-symbols

   ;; Environments
   (LaTeX-add-environments
    ;; 2.3 Building Float Row
    '("floatrow" [ "Number of beside floats" ])

    ;; 6.1 Managing of Float Parts With the subfloatrow Environment
    '("subfloatrow"  [ "Number of beside floats" ])
    '("subfloatrow*" [ "Number of beside floats" ]))

   ;; 2.1.1 Float Box Width Equals to The Width of Object Contents
   (LaTeX-add-lengths "FBwidth" "FBheight" "Xhsize")

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("floatbox"  "[{[[[")
				("ffigbox"   "[[[")
				("ttabbox"   "[[[")
				("fcapside"  "[[["))
			      'textual)
     (font-latex-add-keywords '(("newfloatcommand"           "{{[[")
				("renewfloatcommand"         "{{[[")
				("buildFBBOX"                "{{")
				("floatsetup"                "[{")
				("thisfloatsetup"            "{")
				("clearfloatsetup"           "{")
				("killfloatstyle"            "")
				("DeclareFloatStyle"         "{{")
				("DeclareFloatFont"          "{{")
				("DeclareFloatVCode"         "{{")
				("DeclareColorBox"           "{{")
				("DeclareCBoxCorners"        "{{")
				("DeclareObjectSet"          "{{")
				("DeclareMarginSet"          "{{")
				("DeclareFloatSeparators"    "{{")
				("DeclareFloatFootnoterule"  "{{")
				("newseparatedlabel"         "{{{")
				("newseparatedref"           "{{")
				("makelabelseparator"        "{")
				("DeclareNewFloatType"       "{{")
				("RawFloats"                 ""))
			      'function)))
 LaTeX-dialect)

(defvar LaTeX-floatrow-package-options nil
  "Prompt for package options for the floatrow package.")

;;; floatrow.el ends here
