;;; newtxtt.el --- AUCTeX style for `newtxtt.sty' (v1.05)

;; Copyright (C) 2014 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2014-11-22
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

;; This file adds support for `newtxtt.sty' (v1.05) from 2014/11/18.
;; `newtxtt.sty' is part of TeXLive.

;;; Code:

(TeX-add-style-hook
 "newtxtt"
 (lambda ()

   ;; Run style hook for newtxtt
   (TeX-run-style-hooks "textcomp")

   ;; New symbols
   (TeX-add-symbols
    '("textttz"      t)
    '("ttz"         -1)
    '("ttzdefault"  -1))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("textttz"    "{"))
			      'type-command)
     (font-latex-add-keywords '(("ttzfamily"  "")
				("ttz"        ""))
			      'type-declaration)))
 LaTeX-dialect)

(defvar LaTeX-newtxtt-package-options
  '("scaled" "zerostyle" "nomono" "straightquotes"
    "ttdefault" "ttzdefault")
  "Package options for the newtxtt package.")

;;; newtxtt.el ends here
