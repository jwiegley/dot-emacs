;;; sourcecodepro.el --- AUCTeX style for `sourcecodepro.sty' (v2.6)

;; Copyright (C) 2017 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2017-02-18
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

;; This file adds support for `sourcecodepro.sty' (v2.6) from 2016/04/18.
;; `sourcecodepro.sty' is part of TeXLive.

;;; Code:

(TeX-add-style-hook
 "sourcecodepro"
 (lambda ()

   ;; Load "fontspec" with package options "opentype" or "otf":
   (when (or (LaTeX-provided-package-options-member "sourcecodepro" "opentype")
	     (LaTeX-provided-package-options-member "sourcecodepro" "opentype=true")
	     (LaTeX-provided-package-options-member "sourcecodepro" "otf")
	     (LaTeX-provided-package-options-member "sourcecodepro" "otf=true"))
     (TeX-run-style-hooks "fontspec"))

   ;; The next set of macros is only available when package "fontspec"
   ;; is loaded, by this style or by user.  We just check against
   ;; "fontspec" and do not go through a check of `TeX-engine':
   (when (member "fontspec" (TeX-style-list))
     (TeX-add-symbols
      '("sourcecodepro"        -1)
      '("sourcecodepromedium"  -1)
      '("sourcecodeprolight"   -1)
      '("sourcecodeproextreme" -1)
      '("sourcecodeprolf"      -1)))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup)
	      (member "fontspec" (TeX-style-list)))
     (font-latex-add-keywords '(("sourcecodepro"        "")
				("sourcecodepromedium"  "")
				("sourcecodeprolight"   "")
				("sourcecodeproextreme" "")
				("sourcecodeprolf"      ""))
			      'type-declaration)))
 LaTeX-dialect)

(defvar LaTeX-sourcecodepro-package-options
  '("lining" "nf" "lf"
    "oldstyle" "osf"
    "black" "semibold" "bold"
    "light" "extralight"
    "regular" "medium"
    "scale" "scaled"
    "default" "ttdefault" "nottdefault"
    "type1" "t1"
    "opentype" "otf")
  "Prompt for package options for the sourcecodepro package.")

;;; sourcecodepro.el ends here
