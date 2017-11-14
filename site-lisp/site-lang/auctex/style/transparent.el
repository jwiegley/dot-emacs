;;; transparent.el --- AUCTeX style for `transparent.sty' (v1.0)

;; Copyright (C) 2015 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2015-08-15
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

;; This file adds support for `transparent.sty' (v1.0) from 2007/01/08.
;; `transparent.sty' is part of TeXLive.

;;; Code:

(TeX-add-style-hook
 "transparent"
 (lambda ()
   (TeX-add-symbols
    '("transparent"     "Transparency value (between 0,1)")
    '("texttransparent" "Transparency value (between 0,1)" t))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("transparent"     "{"))
			      'type-declaration)
     (font-latex-add-keywords '(("texttransparent" "{{"))
			      'type-command)))
 LaTeX-dialect)

(defvar LaTeX-transparent-package-options nil
  "Package options for the transparent package.")

;;; transparent.el ends here
