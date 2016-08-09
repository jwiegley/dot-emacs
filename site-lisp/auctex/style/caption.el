;;; caption.el --- AUCTeX style for `caption.sty' (v3.3-111)

;; Copyright (C) 2015 Free Software Foundation, Inc.

;; Author: Arash Esbati <esbati'at'gmx.de>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2015-02-21
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

;; This file adds support for `caption.sty' (v3.3-111) from 2015/09/17.
;; `caption.sty' is part of TeXLive.

;; If things do not work or when in doubt, press `C-c C-n'.  Comments
;; for improvement are welcome.

;;; Code:

;; Needed for compiling `pushnew':
(eval-when-compile (require 'cl))

;; Needed for auto-parsing.
(require 'tex)

(defvar LaTeX-caption-key-val-options
  '(("aboveskip")
    ("belowskip")
    ("font"   ("scriptsize" "footnotesize" "small" "normalsize" "large"
	       "Large" "normalfont" "up" "it" "sl" "sc" "md" "bf" "rm"
	       "sf" "tt" "singlespacing" "onehalfspacing" "doublespacing"
	       "stretch" "normalcolor" "color" "normal"))
    ("font+"  ("scriptsize" "footnotesize" "small" "normalsize" "large"
	       "Large" "normalfont" "up" "it" "sl" "sc" "md" "bf" "rm"
	       "sf" "tt" "singlespacing" "onehalfspacing" "doublespacing"
	       "stretch" "normalcolor" "color" "normal"))
    ("format" ("plain" "hang"))
    ("hangindent")
    ("hypcap" ("false" "no" "off" "0" "true" "yes" "on" "1"))
    ("hypcapspace")
    ("indention")
    ("justification" ("justified" "centering" "centerlast" "centerfirst"
		      "raggedright" "RaggedRight" "raggedleft"))
    ("labelfont"     ("scriptsize" "footnotesize" "small" "normalsize" "large"
		      "Large" "normalfont" "up" "it" "sl" "sc" "md" "bf" "rm"
		      "sf" "tt" "singlespacing" "onehalfspacing" "doublespacing"
		      "stretch" "normalcolor" "color" "normal"))
    ("labelfont+"    ("scriptsize" "footnotesize" "small" "normalsize" "large"
		      "Large" "normalfont" "up" "it" "sl" "sc" "md" "bf" "rm"
		      "sf" "tt" "singlespacing" "onehalfspacing" "doublespacing"
		      "stretch" "normalcolor" "color" "normal"))
    ("labelformat"   ("default" "empty" "simple" "brace" "parens"))
    ("labelsep"      ("none" "colon" "period" "space" "quad" "newline" "endash"))
    ("list"          ("false" "no" "off" "0" "true" "yes" "on" "1"))
    ("listformat"    ("empty" "simple" "paren" "subsimple" "subparens"))
    ("margin")
    ("margin*")
    ("maxmargin")
    ("minmargin")
    ("name")
    ("oneside")
    ("parindent")
    ("parskip")
    ("position"        ("top" "above" "bottom" "below" "auto"))
    ("singlelinecheck" ("false" "no" "off" "0" "true" "yes" "on" "1"))
    ("skip")
    ("strut"      ("false" "no" "off" "0" "true" "yes" "on" "1"))
    ("style"      ("base" "default"))
    ("textfont"   ("scriptsize" "footnotesize" "small" "normalsize" "large"
		   "Large" "normalfont" "up" "it" "sl" "sc" "md" "bf" "rm"
		   "sf" "tt" "singlespacing" "onehalfspacing" "doublespacing"
		   "stretch" "normalcolor" "color" "normal"))
    ("textfont+"  ("scriptsize" "footnotesize" "small" "normalsize" "large"
		   "Large" "normalfont" "up" "it" "sl" "sc" "md" "bf" "rm"
		   "sf" "tt" "singlespacing" "onehalfspacing" "doublespacing"
		   "stretch" "normalcolor" "color" "normal"))
    ("textformat" ("empty" "simple" "period"))
    ("twoside")
    ("type"       ("figure" "table" "ContinuedFloat"))
    ("type*"      ("figure" "table" "ContinuedFloat"))
    ("width"))
  "Key=value options for caption macros.")

(defvar LaTeX-caption-key-val-options-local nil
  "Buffer-local key=value options for caption macros.")
(make-variable-buffer-local 'LaTeX-caption-key-val-options-local)

(defvar LaTeX-caption-supported-float-types
  '("figure" "table" "ContinuedFloat"	; Standard caption.sty
    "sub" "subtable" "subfigure"        ; subcaption.sty
    "ruled" "boxed"			; float.sty
    "floatingfigure" "floatingtable"	; floatflt.sty
    "lstlisting"			; listings.sty
    "longtable"				; longtable.sty
    "figwindow" "tabwindow"		; picinpar.sty
    "parpic"				; picins.sty
    "SCfigure" "SCtable"		; sidecap.sty
    "supertabular" "xtabular"		; supertabular.sty & xtab.sty
    "threeparttable" "measuredfigure"   ; threeparttable.sty
    "wrapfigure" "wraptable")		; wrapfigure
  "List of float types provided by other LaTeX packages and
supported by `caption.sty'.")

;; Setup for various \DeclareCaption's:
(TeX-auto-add-type "caption-DeclareCaption" "LaTeX")

;; The 2. argument to `DeclareCaption[A-Za-z]' contains (La)TeX code.
;; We deliberately ignore that argument in our regex since it is not
;; needed for this style and would pollute the auto generated
;; `docname.el' file.
(defvar LaTeX-caption-DeclareCaption-regexp
  `(,(concat "\\\\DeclareCaption\\(Font\\|Format\\|Justification"
	     "\\|LabelFormat\\|LabelSeparator\\|ListFormat"
	     "\\|Option\\|Style\\|TextFormat\\)"
	     "\\*?"
	     "[ \t\n\r%]*"
	     "{\\([^}]+\\)}")
    (0 1 2) LaTeX-auto-caption-DeclareCaption)
  "Matches the arguments of different `\\DeclareCaption*' from
`caption.sty'.")

(defun LaTeX-caption-auto-prepare ()
  "Clear `LaTeX-auto-caption-DeclareCaption' before parsing."
  (setq	LaTeX-auto-caption-DeclareCaption nil))

(add-hook 'TeX-auto-prepare-hook #'LaTeX-caption-auto-prepare t)
(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)

(defun LaTeX-caption-update-key-val-options ()
  "Update the buffer-local key-val options before offering them
in `caption'-completions."
  (dolist (keyvals (LaTeX-caption-DeclareCaption-list))
    (let* ((key (cond ((string-equal (nth 1 keyvals) "LabelSeparator")
		       (downcase (substring (nth 1 keyvals) 0 8)))
		      (t (downcase (nth 1 keyvals)))))
	   (val (nth 2 keyvals))
	   (val-match (cdr (assoc key LaTeX-caption-key-val-options-local)))
	   (temp (copy-alist LaTeX-caption-key-val-options-local))
	   ;; If `subcaption.el' is loaded, delete and update also the
	   ;; entry for `subrefformat' when processing the `labelformat'.
	   (opts (progn
		   (when (and (string-equal key "labelformat")
			      (boundp 'LaTeX-subcaption-key-val-options))
		     (setq temp
			   (assq-delete-all
			    (car (assoc (caar LaTeX-subcaption-key-val-options) temp))
			    temp)))
		   (assq-delete-all (car (assoc key temp)) temp))))
      ;; For `\DeclareCaptionOption', only add the value
      ;; (remember:      key=^^^^^^, val="defined key")
      (if (string-equal key "option")
	  (pushnew (list val) opts :test #'equal)
	;; For anything but `\DeclareCaptionOption', do the standard
	;; procedure.  Again, take care of `subrefformat' for `subcaption.el'.
	(if val-match
	    (progn
	      (when (and (string-equal key "labelformat")
			 (boundp 'LaTeX-subcaption-key-val-options))
		(pushnew (list "subrefformat"
			       (delete-dups (apply 'append (list val) val-match)))
			 opts :test #'equal))
	      (pushnew (list key (delete-dups (apply 'append (list val) val-match)))
		       opts :test #'equal))
	  (pushnew (list key (list val)) opts :test #'equal)))
      (setq LaTeX-caption-key-val-options-local (copy-alist opts)))))

(defun LaTeX-arg-caption-command (optional &optional prompt)
  "Insert caption-commands from `caption.sty'. If OPTIONAL,
indicate `(Optional)' while reading key=val and insert it in
square brackets.  PROMPT replaces the standard one."
  (LaTeX-caption-update-key-val-options)
  (let ((opts (TeX-read-key-val optional
				LaTeX-caption-key-val-options-local
				prompt)))
    (TeX-argument-insert opts optional)))

;; In `LaTeX-caption-DeclareCaption-regexp', we match (0 1 2).  When
;; adding a new `Name', we need something unique for `0'-match until
;; the next `C-c C-n'.  We mimic that regex-match bei concat'ing the
;; elements.  It will vanish upon next `C-c C-n'.
(defun LaTeX-arg-caption-DeclareCaption (optional format)
  "Insert various `\\DeclareCaptionFORMAT' commands.  If
OPTIONAL, insert argument in square brackets.  FORMAT is the
suffix of the command."
  (let ((name (TeX-read-string "Name: ")))
    (LaTeX-add-caption-DeclareCaptions
     (list (concat "\\DeclareCaption" format "{" name "}")
	   format name))
    (TeX-argument-insert name optional)))

;; Support for an undocumented feature of caption.sty:
;; `\captionbox' sets the width of the caption equal to the width of
;; the contents (a feature provided e.g. by `threeparttable.sty').
;; The starred version typesets the caption without label and without
;; entry to the list of figures or tables.

;; The first mandatory argument {<heading>} contains the caption text
;; and the label.  We use `TeX-insert-macro' to do the job. (Thanks to
;; M. Giordano for his valuable comments on this!)

;; Syntax:
;; \captionbox[<list entry>]{<heading>}[<width>][<inner-pos>]{<contents>}
;; \captionbox*{<heading>}[<width>][<inner-pos>]{<contents>}

(defun LaTeX-arg-caption-captionbox (optional &optional star prompt)
  "Query for the arguments of `\\captionbox' incl. a label and
insert them.  If STAR is non-nil, then do not query for a `\\label' and
insert only a caption."
  (let ((caption (TeX-read-string
		  (TeX-argument-prompt optional prompt "Caption"))))
    (LaTeX-indent-line)
    (insert TeX-grop caption)
    (unless star (TeX-insert-macro "label"))
    (insert TeX-grcl))
  (let* ((width (completing-read (TeX-argument-prompt t prompt "Width")
				 (mapcar (lambda(elt) (concat TeX-esc (car elt)))
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
 "caption"
 (lambda ()

   ;; Add caption to the parser.
   (TeX-auto-add-regexp LaTeX-caption-DeclareCaption-regexp)

   ;; Activate the buffer-local version of key-vals.
   (setq LaTeX-caption-key-val-options-local
	 (copy-alist LaTeX-caption-key-val-options))

   ;; Caption commands:
   (TeX-add-symbols
    '("caption*" t)

    '("captionlistentry"
      [TeX-arg-eval completing-read (TeX-argument-prompt t nil "Float type")
		    LaTeX-caption-supported-float-types]
      t)

    '("captionof"
      (TeX-arg-eval completing-read (TeX-argument-prompt nil nil "Float type")
		    LaTeX-caption-supported-float-types)
      ["List entry"] t)

    '("captionof*"
      (TeX-arg-eval completing-read (TeX-argument-prompt nil nil "Float type")
		    LaTeX-caption-supported-float-types)
      ["List entry"] t)

    '("captionsetup"
      [TeX-arg-eval completing-read (TeX-argument-prompt t nil "Float type")
		    LaTeX-caption-supported-float-types]
      (LaTeX-arg-caption-command))

    '("captionsetup*"
      [TeX-arg-eval completing-read (TeX-argument-prompt t nil "Float type")
		    LaTeX-caption-supported-float-types]
      (LaTeX-arg-caption-command))

    '("clearcaptionsetup"
      [LaTeX-arg-caption-command "Single key"]
      (TeX-arg-eval completing-read (TeX-argument-prompt nil nil "Float type")
		    LaTeX-caption-supported-float-types))

    '("clearcaptionsetup*"
      [LaTeX-arg-caption-command "Single key"]
      (TeX-arg-eval completing-read (TeX-argument-prompt nil nil "Float type")
		    LaTeX-caption-supported-float-types))

    '("captionbox"  ["List entry"] (LaTeX-arg-caption-captionbox) t)

    '("captionbox*" (LaTeX-arg-caption-captionbox t) t)

    '("ContinuedFloat" 0)
    '("ContinuedFloat*" 0)

    '("continuedfloat" 0)
    '("continuedfloat*" 0)

    '("DeclareCaptionFont"
      (LaTeX-arg-caption-DeclareCaption "Font") t)

    '("DeclareCaptionFormat"
      (LaTeX-arg-caption-DeclareCaption "Format") t)

    '("DeclareCaptionFormat*"
      (LaTeX-arg-caption-DeclareCaption "Format") t)

    '("DeclareCaptionJustification"
      (LaTeX-arg-caption-DeclareCaption "Justification") t)

    '("DeclareCaptionLabelFormat"
      (LaTeX-arg-caption-DeclareCaption "LabelFormat") t)

    '("DeclareCaptionLabelSeparator"
      (LaTeX-arg-caption-DeclareCaption "LabelSeparator") t)

    '("DeclareCaptionLabelSeparator*"
      (LaTeX-arg-caption-DeclareCaption "LabelSeparator") t)

    '("DeclareCaptionListFormat"
      (LaTeX-arg-caption-DeclareCaption "ListFormat") t)

    '("DeclareCaptionOption"
      (LaTeX-arg-caption-DeclareCaption "Option") t)

    '("DeclareCaptionStyle"
      (LaTeX-arg-caption-DeclareCaption "Style")
      [LaTeX-arg-caption-command "Additional options"]
      (LaTeX-arg-caption-command "Options"))

    '("DeclareCaptionTextFormat"
      (LaTeX-arg-caption-DeclareCaption "TextFormat") t)

    '("bothIfFirst" 2)

    '("bothIfSecond" 2))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("caption"           "*[{")
				("captionlistentry"  "[{")
				("captionof"         "*{[{")
				("captionbox"        "*[{[[{"))
			      'textual)
     (font-latex-add-keywords '(("captionsetup"                  "*[{")
				("clearcaptionsetup"             "*[{")
				("DeclareCaptionFont"            "{{")
				("DeclareCaptionFormat"          "*{{")
				("DeclareCaptionJustification"   "{{")
				("DeclareCaptionLabelFormat"     "{{")
				("DeclareCaptionLabelSeparator"  "*{{")
				("DeclareCaptionListFormat"      "{{")
				("DeclareCaptionOption"          "{{")
				("DeclareCaptionStyle"           "{[{")
				("DeclareCaptionTextFormat"      "{{"))
			      'function)) )
 LaTeX-dialect)

(defun LaTeX-caption-package-options ()
  "Prompt for package options for the caption package."
  (TeX-read-key-val t
   (append '(("compatibility"  ("true" "false")))
	   '(("figureposition" ("top" "above" "bottom" "below")))
	   '(("tableposition"  ("top" "above" "bottom" "below")))
	   LaTeX-caption-key-val-options)))

;;; caption.el ends here
