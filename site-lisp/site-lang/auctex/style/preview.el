;;; preview.el --- AUCTeX style for `preview.sty' (v2010/02/14)

;; Copyright (C) 2017 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2017-02-05
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

;; This file adds support for `preview.sty' v2010/02/14.
;; `preview.sty' is part of TeXLive.

;;; Code:

(defun LaTeX-preview-arg-ifpreview (_optional)
  "Insert \\else and \\fi part of \\ifPreview command from preview.sty.
OPTIONAL is ignored."
  (indent-according-to-mode)
  (LaTeX-newline)
  (indent-according-to-mode)
  (save-excursion
    (LaTeX-newline)
    (indent-according-to-mode)
    (insert TeX-esc "else")
    (LaTeX-newline)
    (LaTeX-newline)
    (indent-according-to-mode)
    (insert TeX-esc "fi")))

(TeX-add-style-hook
 "preview"
 (lambda ()

   (LaTeX-add-environments
    '("preview")
    '("nopreview"))

   (TeX-add-symbols
    '("PreviewMacro" (TeX-arg-conditional (y-or-n-p "With optional arguments? ")
					  ( [ t ] [ nil ] )
					())
      TeX-arg-macro)

    '("PreviewMacro*" (TeX-arg-conditional (y-or-n-p "With optional arguments? ")
					   ( [ t ] [ nil ] )
					 ())
      TeX-arg-macro)

    '("PreviewEnvironment" (TeX-arg-conditional (y-or-n-p "With optional arguments? ")
						( [ t ] [ nil ] )
					      ())
      TeX-arg-environment)

    '("PreviewEnvironment*" (TeX-arg-conditional (y-or-n-p "With optional arguments? ")
						 ( [ t ] [ nil ] )
					       ())
      TeX-arg-environment)

    '("PreviewSnarfEnvironment" TeX-arg-environment)

    '("PreviewOpen")
    '("PreviewClose")

    '("ifPreview" LaTeX-preview-arg-ifpreview))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("PreviewMacro"            "*[[{")
				("PreviewEnvironment"      "*[[{")
				("PreviewSnarfEnvironment" "{"))
			      'function)))
 LaTeX-dialect)

(defvar LaTeX-preview-package-options
  '("active"      "noconfig"   "psfixbb"
    "dvips"       "pdftex"     "xetex"
    "displaymath" "floats"     "textmath"
    "graphics"    "sections"   "delayed"
    "auctex"      "showlabels" "tightpage"
    "lyx"         "counters"   "footnotes"
    "tracingall"  "showbox")
  "Package options for the preview package.")

;;; preview.el ends here
