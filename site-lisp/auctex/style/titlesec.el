;;; titlesec.el --- AUCTeX style for `titlesec.sty' (v2.10.0)

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

;; This file adds support for `titlesec.sty' (v2.10.0) from
;; 2011/12/15.  `titlesec.sty' is part of TeXLive.

;;; Code:

(defvar LaTeX-titlesec-key-val-options
  '(("page" ("even" "odd"))
    ("numberless"))
  "Key=value options for \"\\titleformat\" and \"\\titlespacing\"
macros provided by \"titlesec.sty\".")

(defvar LaTeX-titlesec-section-command-list
  '("part"
    "chapter"
    "section"
    "subsection"
    "subsubsection"
    "paragraph"
    "subparagraph")
  "List of sectioning commands available in \"titlesec.sty\".")

(defvar LaTeX-titlesec-section-shape-list
  '("hang"
    "block"
    "display"
    "runin"
    "leftmargin"
    "rightmargin"
    "drop"
    "wrap"
    "frame")
  "List of sectioning shapes available for \"\\titleformat\" command.")

(defun LaTeX-titlesec-section-command-list ()
  "Remove \"chapter\" from variable
`LaTeX-titlesec-section-command-list' and return the remainder.
Removal is based on the return value of function
`LaTeX-largest-level'.  Items returned are prefixed with
`TeX-esc'."
  (mapcar (lambda (elt) (concat TeX-esc elt))
	  (if (< (LaTeX-largest-level) 2)
	      (symbol-value 'LaTeX-titlesec-section-command-list)
	    (remove "chapter" LaTeX-titlesec-section-command-list))))

(defun LaTeX-arg-titlesec-titlespec (optional)
  "Insert the first argument of \"\\titleformat\" and \"\\titlespacing\".
Depending on returned value of function `LaTeX-largest-level',
append a \"name\" key with corresponding values to
`LaTeX-titlesec-key-val-options'.  The values are retrieved from
`LaTeX-titlesec-section-command-list'.  The values of this list
are also added stand-alone as keys.  If OPTIONAL is non-nil,
insert the argument in brackets."
  (let ((keyvals
	 (TeX-read-key-val
	  optional
	  (append
	   `(("name"
	      ,(mapcar (lambda (elt) (concat TeX-esc elt))
		       (if (< (LaTeX-largest-level) 2)
			   (symbol-value 'LaTeX-titlesec-section-command-list)
			 (remove "chapter" LaTeX-titlesec-section-command-list)))))
	   (mapcar #'list
		   (mapcar (lambda (elt) (concat TeX-esc elt))
			   (if (< (LaTeX-largest-level) 2)
			       (symbol-value 'LaTeX-titlesec-section-command-list)
			     (remove "chapter" LaTeX-titlesec-section-command-list))))
	   LaTeX-titlesec-key-val-options)
	  "Sectioning command")))
    (TeX-argument-insert keyvals optional)))

(TeX-add-style-hook
 "titlesec"
 (lambda ()

   ;; Load "titleps.el" when "pagestyles" package option is given
   (when (LaTeX-provided-package-options-member "titlesec" "pagestyles")
     (TeX-run-style-hooks "titleps"))

   (TeX-add-symbols
    ;; 2.4. Tools
    '("titlelabel" t)

    ;; \titleformat*{<command>}{<format>}
    '("titleformat*" (LaTeX-arg-titlesec-titlespec) t)

    ;; 3. Advanced Interface
    ;; \titleformat{<command>}[<shape>]{<format>}{<label>}{<sep>}{<before-code>}[<after-code>]
    '("titleformat"
      (LaTeX-arg-titlesec-titlespec)
      [TeX-arg-eval completing-read
		     (TeX-argument-prompt optional nil "Shape")
		     LaTeX-titlesec-section-shape-list]
      (TeX-arg-conditional (y-or-n-p "With optional after-code? ")
			   (4 [nil])
			 (4)))

    '("chaptertitlename" 0)

    ;; 3.2. Spacing
    ;; \titlespacing{<command>}{<left>}{<before-sep>}{<after-sep>}[<right-sep>]
    '("titlespacing"
      (LaTeX-arg-titlesec-titlespec)
      (TeX-arg-length "Left margin")
      (TeX-arg-length "Before vertical space")
      (TeX-arg-length "Space between title and text")
      [TeX-arg-length "Right margin"])

    '("titlespacing*"
      (LaTeX-arg-titlesec-titlespec)
      (TeX-arg-length "Left margin")
      (TeX-arg-length "Before vertical space")
      (TeX-arg-length "Space between title and text")
      [TeX-arg-length "Right margin"])

    ;; 3.3. Spacing related tools
    '("filright"  0)
    '("filcenter" 0)
    '("filleft"	  0)
    '("fillast"   0)
    '("filinner"  0)
    '("filouter"  0)
    '("wordsep"	  0)

    ;; 3.4. Rules
    '("titleline"
      [TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Alignment")
		    '("l" "r" "c")]
      t)

    '("titlerule" [TeX-arg-length "Rule height"])

    '("titlerule*" [TeX-arg-length "Box width"] "Text")

    '("iftitlemeasuring" 2)

    ;; 3.5. Page styles
    '("assignpagestyle"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Sectioning command")
		    (LaTeX-titlesec-section-command-list))
      (TeX-arg-pagestyle))

    ;; 3.9. Creating new levels and changing the class
    '("titleclass"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Sectioning command")
		    (LaTeX-titlesec-section-command-list))
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Class")
		    '("page" "top" "straight"))
      [TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Super level command")
		    (LaTeX-titlesec-section-command-list)]) )

   ;; 3.4. Rules: A variant of \titleline to be used only with calcwidth
   (when (LaTeX-provided-package-options-member "titlesec" "calcwidth")
     (TeX-add-symbols
      '("titleline*"
	(TeX-arg-eval completing-read
		      (TeX-argument-prompt optional nil "Alignment")
		      '("l" "r" "c"))
	t)))

   ;; The length of the longest line is returned in \titlewidth
   (LaTeX-add-lengths "titlewidth"
		      "titlewidthlast"
		      "titlewidthfirst")

   ;; Fontification: We only add macros which are used at top level;
   ;; most of macros definded above are intended to be used in
   ;; arguments of \titleformat
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("titlelabel"        "{")
				;;
				;; \titleformat comes in 2 flavors:
				;; with *, it takes only 2 mandatory
				;; argument; w/o *, a lot more.  It is
				;; not (yet) possible to realize this
				;; behaviour within font-latex.  Hence
				;; we reduce the fontification to the
				;; first 2 mandatory arguments and
				;; ignore the rest.  *[ are optional anyway.
				("titleformat"       "*{[{")
				("titlespacing"      "*{{{{[")
				("iftitlemeasuring"  "{{")
				("assignpagestyle"   "{{")
				("titleclass"        "{[{["))
			      'function)))
 LaTeX-dialect)

(defvar LaTeX-titlesec-package-options
  '(;; 2.1. Format
    "rm" "sf" "tt" "md" "bf" "up" "it" "sl" "sc"
    "big" "medium" "small" "tiny"
    "raggedleft" "center" "raggedright"

    ;; 2.2. Spacing
    "compact"

    ;; 2.3. Uppercase
    "uppercase"

    ;; 3.3. Spacing related tools
    "indentafter"   "noindentafter"
    "rigidchapters" "rubberchapters"
    "bottomtitles"  "nobottomtitles" "nobottomtitles*"
    "aftersep"      "largestsep"     "pageatnewline"

    ;; 3.4. Rules
    "calcwidth"

    ;; 3.7. Other Package Options
    "explicit"
    "newparttoc"
    "oldparttoc"
    "clearempty"
    "toctitles"
    "newlinetospace"
    "loadonly"

    ;; 5. titleps and Page Styles
    "pagestyles")
  "Package options for the titlesec package.")

;;; titlesec.el ends here
