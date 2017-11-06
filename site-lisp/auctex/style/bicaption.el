;;; bicaption.el --- AUCTeX style for `bicaption.sty' (v1.1-158)

;; Copyright (C) 2016, 2017 Free Software Foundation, Inc.

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

;; This file adds support for `bicaption.sty' (v1.1-158) from
;; 2016/03/27.  `bicaption.sty' is part of TeXLive.

;; If things do not work or when in doubt, press `C-c C-n'.  Comments
;; for improvement are welcome.

;;; Code:

(defvar LaTeX-bicaption-key-val-options
  '(("bi-lang" ("first" "second" "both"))
    ("bi-singlelinecheck" ("false" "no" "off" "0" "true" "yes" "on" "1"))
    ("bi-slc" ("false" "no" "off" "0" "true" "yes" "on" "1"))
    ("bi-swap" ("false" "no" "off" "0" "true" "yes" "on" "1"))
    ("listtype+"))
  "Key=value options for bicaption macros.")

(defun LaTeX-arg-bicaption-bicaption (optional &optional prompt star cap-box label-inside)
  "Query for the arguments of \"\\bicaption\" incl. a label and insert them.
PROMPT replaces the standard one.  If STAR is non-nil, then do
not query for a \\label and short captions, insert only captions.
If CAP-BOX is non-nil, also query and include optional arguments
for the box command.  If LABEL-INSIDE is non-nil, insert \\label
inside the first mandatory argument, otherwise after all
arguments."
  (let* (;; \bisubcaption needs an environment, "minipage" will be
	 ;; popular.  If so, check next higher environment to find out
	 ;; where we are
	 (currenv (if (string= (LaTeX-current-environment) "minipage")
		      (LaTeX-current-environment 2)
		    (LaTeX-current-environment)))
	 (captionI (TeX-read-string
		    (TeX-argument-prompt
		     optional (when prompt
				(concat "1. " prompt "bicaption"))
		     "1. bicaption")))
	 (short-captionI
	  (when (and (not star)
		     (>= (length captionI) LaTeX-short-caption-prompt-length))
	    (TeX-read-string
	     (TeX-argument-prompt t (when prompt
				      (concat "Short 1. " prompt "bicaption"))
				  "Short 1. bicaption"))))
	 (captionII (TeX-read-string
		     (TeX-argument-prompt
		      optional (when prompt
				 (concat "2. " prompt "bicaption"))
		      "2. bicaption")))
	 (short-captionII
	  (when (and (not star)
		     (>= (length captionII) LaTeX-short-caption-prompt-length))
	    (TeX-read-string
	     (TeX-argument-prompt t (when prompt
				      (concat "Short 2. " prompt "bicaption"))
				  "Short 2. bicaption")))))
    (indent-according-to-mode)
    ;; Insert short & regular 1. caption
    (when (and short-captionI (not (string= short-captionI "")))
      (insert LaTeX-optop short-captionI LaTeX-optcl))
    (insert TeX-grop captionI)
    ;; For \bi(sub)?captionbox, the label must be inserted here
    (when (and label-inside (not star))
      (LaTeX-label currenv 'environment))
    (insert TeX-grcl)
    (LaTeX-fill-paragraph)
    (LaTeX-newline)
    (indent-according-to-mode)
    ;; Insert short & regular 2. caption
    (when (and short-captionII (not (string= short-captionII "")))
      (insert LaTeX-optop short-captionII LaTeX-optcl))
    (insert TeX-grop captionII TeX-grcl)
    ;; Insert width & pos in case of captionbox macros:
    (when cap-box
      (let* ((TeX-arg-opening-brace "[")
	     (TeX-arg-closing-brace "]")
	     (width (completing-read (TeX-argument-prompt t nil "Width")
				     (mapcar (lambda (elt) (concat TeX-esc (car elt)))
					     (LaTeX-length-list))))
	     (inpos (if (and width (not (string-equal width "")))
			(completing-read (TeX-argument-prompt t nil "Inner position")
					 '("c" "l" "r" "s"))
		      "")))
	(TeX-argument-insert width t)
	(TeX-argument-insert inpos t)))
    (LaTeX-fill-paragraph)
    ;; Insert label -- a new line is inserted only if label is there:
    (when (and (not label-inside) (not star)
	       (save-excursion (LaTeX-label currenv 'environment)))
      (LaTeX-newline)
      (indent-according-to-mode)
      (end-of-line))))

(defun LaTeX-arg-bicaption-captionsetup (optional)
  "Query for 2 arguments for \"\\captionsetup\" with bicaption.sty loaded.
When OPTIONAL is non-nil, include both as optional arguments in
square brackets."
  (let* ((flttype (completing-read (TeX-argument-prompt optional nil "Float type")
				  LaTeX-caption-supported-float-types))
	 (biflt (if (and (not (or (string= flttype "bi")
				  (string= flttype "bi-first")
				  (string= flttype "bi-second")))
			 flttype (not (string= flttype "")))
		    (completing-read (TeX-argument-prompt optional nil "Bicaption type")
				     '("bi" "bi-first" "bi-second"))
		  "")))
    (TeX-argument-insert flttype optional)
    (TeX-argument-insert biflt optional)))

(TeX-add-style-hook
 "bicaption"
 (lambda ()

   ;; Load caption.el:
   (TeX-run-style-hooks "caption")

   ;; Macros
   (TeX-add-symbols
    '("bicaption"        (LaTeX-arg-bicaption-bicaption))
    '("bicaption*"       (LaTeX-arg-bicaption-bicaption  nil    t))
    '("bicaptionbox"     (LaTeX-arg-bicaption-bicaption  nil   nil  t   t) t)
    '("bicaptionbox*"    (LaTeX-arg-bicaption-bicaption  nil    t   t)     t)
    '("bisubcaption"     (LaTeX-arg-bicaption-bicaption "sub-"))
    '("bisubcaption*"    (LaTeX-arg-bicaption-bicaption "sub-"  t))
    '("bisubcaptionbox"  (LaTeX-arg-bicaption-bicaption "sub-" nil  t   t) t)
    '("bisubcaptionbox*" (LaTeX-arg-bicaption-bicaption "sub-"  t   t   t) t))

   ;; \bi(sub)?caption(box)? macros should get their own lines
   (LaTeX-paragraph-commands-add-locally '("bicaption"    "bicaptionbox"
					   "bisubcaption" "bisubcaptionbox"))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("bicaption"       "*[{[{")
				("bicaptionbox"    "*[{[{[[")
				("bisubcaption"    "*[{[{")
				("bisubcaptionbox" "*[{[{[["))
			      'textual)))
 LaTeX-dialect)

(defun LaTeX-bicaption-package-options ()
  "Prompt for package options for the bicaption package."
  (TeX-read-key-val t
		    (append
		     `(,(list "language"
			      (cond ((and (member "babel" (TeX-style-list))
					  (LaTeX-babel-active-languages))
				     (butlast (LaTeX-babel-active-languages)))
				    ((and (member "polyglossia" (TeX-style-list))
					  (LaTeX-polyglossia-active-languages))
				     (butlast (LaTeX-babel-active-languages)))
				    (t nil))))
		     LaTeX-bicaption-key-val-options
		     LaTeX-caption-key-val-options)))

;;; bicaption.el ends here
