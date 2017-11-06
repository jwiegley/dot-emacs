;;; MyriadPro.el --- AUCTeX style for `MyriadPro.sty' (v0.5)

;; Copyright (C) 2014 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2014-10-21
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

;; This file adds support for `MyriadPro.sty' (v0.5) from 2013/04/20.
;; The latest version of MyriadPro is available as part of FontPro
;; bundle from <https://www.github.com/sebschub>.  `MyriadPro.sty' is
;; not part of TeXLive.

;;; Code:

(TeX-add-style-hook
 "MyriadPro"
 (lambda ()

   ;; Run style hook for various packages loaded by MyriadPro
   (TeX-run-style-hooks "textcomp" "amsmath" "fontaxes" "mdsymbol")

   ;; New symbols
   (TeX-add-symbols
    '("smallfrac" "Numerator" "Denominator")
    '("slantfrac" "Numerator" "Denominator")
    '("boldsymbol" "Symbol"))

   ;; More control over spacing in `\slantfrac':
   (LaTeX-add-lengths "MdSlantfracSpacingBeforeSlash"
		      "MdSlantfracSpacingAfterSlash")

   ;; `\mathversion' is available with sansmath option
   (when (LaTeX-provided-package-options-member "MyriadPro" "sansmath")
     (TeX-add-symbols
      '("mathversion"
	(TeX-arg-eval completing-read "Math version: "
		      '(("sans")        ("sansbold")
			("sanstabular") ("sansboldtabular"))))))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("smallfrac"   "{{")
				("slantfrac"   "{{"))
			      'textual)
     (font-latex-add-keywords '(("mathversion" "{"))
			      'variable)))
 LaTeX-dialect)

(defvar LaTeX-MyriadPro-package-options
  '(;; Font selection
    "smallfamily" "medfamily" "onlytext" "onlymath" "math" "sansmath"

    ;; Figure selection
    "textosf" "mathosf" "osf" "textlf" "mathlf" "lf" "mathtabular"

    ;; Calligraphic fonts
    "cmsy" "swash" "abx"

    ;; Blackboard bold letters
    "amsbb" "fourierbb" "lucidabb"

    ;; Greek letters
    "mixedgreek" "italicgreek" "frenchmath"

    ;; Miscellaneous options
    "scale" "loosequotes" "footnotefigures"

    ;; Additional mathversions
    "sansmath")
  "Package options for the MyriadPro package.")

;;; MyriadPro.el ends here
