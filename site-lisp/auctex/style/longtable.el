;;; longtable.el --- AUCTeX style for `longtable.sty'.

;; Copyright (C) 2013--2016  Free Software Foundation, Inc.

;; Maintainer: auctex-devel@gnu.org
;; Author: Mosè Giordano <mose@gnu.org>
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

;; This file adds support for `longtable.sty'.

;;; Code:

(defvar LaTeX-longtable-skipping-regexp
  (regexp-opt '("[l]" "[r]" "[c]" ""))
  "Regexp matching between \\begin{longtable} and column specification.
For longtable environments only.")

(defun LaTeX-item-longtable (&optional suppress)
  "Insert line break macro on the last line and suitable number of &'s.
For longtable environments.  If SUPPRESS is non-nil, do not
insert line break macro."
  (unless suppress
    (save-excursion
      (end-of-line 0)
      (just-one-space)
      (TeX-insert-macro "\\")))
  (LaTeX-insert-ampersands
   LaTeX-longtable-skipping-regexp #'LaTeX-array-count-columns))

(TeX-add-style-hook
 "longtable"
 (lambda ()
   (LaTeX-add-environments
    '("longtable" (lambda (environment)
		    (let* ((pos (completing-read (TeX-argument-prompt t nil "Position")
						 '(("l") ("r") ("c"))))
			   (fmt (TeX-read-string "Format: " LaTeX-default-format))
			   (caption (TeX-read-string "Caption: "))
			   (short-caption (when (>= (length caption) LaTeX-short-caption-prompt-length)
					    (TeX-read-string "(Optional) Short caption: "))))
		      (setq LaTeX-default-format fmt)
		      (LaTeX-insert-environment environment
						(concat
						 (unless (zerop (length pos))
						   (concat LaTeX-optop pos LaTeX-optcl))
						 (concat TeX-grop fmt TeX-grcl)))
		      ;; top caption -- do nothing if user skips caption
		      (unless (zerop (length caption))
			;; insert `\caption[short-caption]{caption':
			(insert TeX-esc "caption")
			(when (and short-caption (not (string= short-caption "")))
			  (insert LaTeX-optop short-caption LaTeX-optcl))
			(insert TeX-grop caption)
			;; ask for a label and insert it
			(LaTeX-label environment 'environment)
			;; the longtable `\caption' is equivalent to a
			;; `\multicolumn', so it needs a `\\' at the
			;; end of the line.  Prior to that, add } to
			;; close `\caption{'
			(insert TeX-grcl "\\\\")
			;; fill the caption
			(LaTeX-fill-paragraph)
			;; Insert a new line and indent
			(LaTeX-newline)
			(indent-according-to-mode))
		      ;; Insert suitable number of &'s, suppress line break
		      (LaTeX-item-longtable t)))))

   (TeX-add-symbols
    ;; Commands to end table rows
    '("endhead" 0)
    '("endfirsthead" 0)
    '("endfoot" 0)
    '("endlastfoot" 0)
    ;; Caption commands
    '("caption*" 1))

   ;; These parameters are set with \setlength
   (LaTeX-add-lengths
    "LTleft" "LTright" "LTpre" "LTpost" "LTcapwidth")

   ;; This parameter is set with \setcounter
   (LaTeX-add-counters "LTchunksize")

   ;; Use the enhanced table formatting.  Append to
   ;; `LaTeX-indent-environment-list' in order not to override custom settings.
   (add-to-list (make-variable-buffer-local 'LaTeX-indent-environment-list)
		'("longtable" LaTeX-indent-tabular) t)

   ;; Append longtable to `LaTeX-label-alist', in order not to override possible
   ;; custome values.
   (add-to-list 'LaTeX-label-alist '("longtable" . LaTeX-table-label) t)

   ;; Append longtable to `LaTeX-item-list' with `LaTeX-item-longtable'
   (add-to-list 'LaTeX-item-list '("longtable" . LaTeX-item-longtable) t)

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     ;; Actually, `\caption*{}' macro takes only one mandatory
     ;; argument, not an optional one, the following is a workaround
     ;; to fontify correctly also the standard `\caption[]{}' macro.
     (font-latex-add-keywords '(("caption" "*[{"))
			      'textual)))
 LaTeX-dialect)

;; `longtable.sty' has two options "errorshow" and "pausing", both for
;; debugging purposes.  We ignore them both in order to make package
;; loading faster in a buffer.
(defvar LaTeX-longtable-package-options nil
  "Package options for the longtable package.")

;; longtable.el ends here
