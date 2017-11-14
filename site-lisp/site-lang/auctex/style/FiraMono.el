;;; FiraMono.el --- AUCTeX style for `FiraMono.sty' (v2016/02/13)

;; Copyright (C) 2016 Free Software Foundation, Inc.

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

;; This file adds support for `FiraMono.sty' (v2016/02/13).
;; `FiraMono.sty' is part of TeXLive.

;;; Code:

(TeX-add-style-hook
 "FiraMono"
 (lambda ()

   ;; `textcomp' is always loaded:
   (TeX-run-style-hooks "textcomp")

   ;; If package option `type1' is given, load `fontaxes':
   (when (LaTeX-provided-package-options-member "FiraMono" "type1")
     (TeX-run-style-hooks "fontaxes"))

   ;; Macros:
   (TeX-add-symbols
    '("sufigures"        -1)
    '("firamonooldstyle" -1)
    '("firamonolining"   -1)
    '("firamonomedium"   -1))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("sufigures"        "")
				("firamonooldstyle" "")
				("firamonolining"   "")
				("firamonomedium"   ""))
			      'type-declaration)))
 LaTeX-dialect)

(defvar LaTeX-FiraMono-package-options '("scaled" "scale"
					 "type1"
					 "lining" "lf"
					 "oldstyle" "osf"
					 "nomap"
					 "medium" "mb")
  "Package options for the FiraMono package.")

;;; FiraMono.el ends here
