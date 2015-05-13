;;; MinionPro.el -- AUCTeX style for MinionPro.sty

;; Copyright (C) 2005, 2014 Free Software Foundation, Inc.

;; Author: Mark Trettin <Mark.Trettin@gmx.de>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2005-11-26
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

;; This file adds support for `MinionPro.sty' (v2.3) from 2012/08/03.
;; The latest version of MinionPro is available as part of FontPro
;; bundle from <https://www.github.com/sebschub>.

;;; Code:

(TeX-add-style-hook
 "MinionPro"
 (lambda ()

   ;; New symbols
   (TeX-add-symbols
    '("smallfrac" "Numerator" "Denominator")
    '("slantfrac" "Numerator" "Denominator"))

   ;; Run style hook for amsmath which is loaded via MnSymbol
   (TeX-run-style-hooks "amsmath" "fontaxes" "textcomp")

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("smallfrac" "{{")
				("slantfrac" "{{"))
			      'textual)))
 LaTeX-dialect)

(defvar LaTeX-MinionPro-package-options
  '("smallfamily" "medfamily" "fullfamily" "noopticals" "opticals"
    "slides" "textosf" "mathosf" "osf" "textlf" "mathlf" "lf"
    "mathtabular" "mnsy" "cmsy" "swash" "abx" "amsbb" "fourierbb"
    "lucidabb" "mixedgreek" "italicgreek" "frenchmath" "minionint"
    "footnotefigures"

    ;; Additional options in v2.1
    "onlytext" "onlymath" "loosequotes" "openg" "normalsize" "nonormalsize"

    ;; Additional option in v2.2
    "scale")
  "Package options for the MinionPro package.")

;;; MinionPro.el ends here
