;;; erewhon.el --- AUCTeX style for `erewhon.sty' (v1.04)

;; Copyright (C) 2014, 2015 Free Software Foundation, Inc.

;; Author: Arash Esbati <esbati'at'gmx.de>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2014-11-18
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

;; This file adds support for `erewhon.sty' (v1.04) from 2015/04/07.
;; `erewhon.sty' is part of TeXLive.

;;; Code:

(TeX-add-style-hook
 "erewhon"
 (lambda ()

   ;; Run style hook for various packages loaded by erewhon
   (TeX-run-style-hooks "textcomp" "fontaxes")

   ;; New symbols
   (TeX-add-symbols

    ;; Only preamble commands
    '("useosf"  0)
    '("useproportional" 0)

    ;; Text commands
    '("lfstyle"   -1)   ; lf declaration
    '("tlfstyle"  -1)   ; tlf declaration
    '("osfstyle"  -1)   ; osf declaration
    '("tosfstyle" -1)   ; tosf declaration
    '("sufigures" -1)   ; superior figures declaration
    '("textlf"     t)   ; proportional lining figures
    '("texttlf"    t)   ; tabular lining figures
    '("textosf"    t)   ; proportional oldstyle figures
    '("texttosf"   t)   ; tabular oldstyle figures
    '("textsu"     t)   ; superior figures
    '("textin"     t)   ; inferior figures
    '("textnu"     t)   ; numerator figures
    '("textde"     t)   ; denominator figures
    '("textfrac" "Numerator" "Denominator"))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("textlf"    "{")
				("texttlf"   "{")
				("textosf"   "{")
				("texttosf"  "{")
				("textsu"    "{")
				("textin"    "{")
				("textnu"    "{")
				("textde"    "{"))
			      'type-command)
     (font-latex-add-keywords '(("lfstyle"   "")
				("tlfstyle"  "")
				("osfstyle"  "")
				("tosfstyle" "")
				("sufigures" ""))
			      'type-declaration)
     (font-latex-add-keywords '(("textfrac"  "{{"))
			      'textual)))
 LaTeX-dialect)

(defvar LaTeX-erewhon-package-options
  '("lining" "lf" "oldstyle" "osf" "tabular" "p" "proportional"
    "scale" "scaled" "scosf" "space" "sups")
  "Package options for the erewhon package.")

;;; erewhon.el ends here
