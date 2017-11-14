;;; fontenc.el --- AUCTeX style for `fontenc.sty' (v1.99g)

;; Copyright (C) 2015 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2015-09-12
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

;; This file adds support for `fontenc.sty' (v1.99g) from 2005/09/27.
;; `fontenc.sty' is a standard LaTeX package and part of TeXLive.

;;; Code:

(defvar LaTeX-fontenc-package-options-list
  '(;; 128+ glyph encodings (text)
    "OT1" "OT2" "OT3" "OT4" "OT6"
    ;; 256 glyph encodings (text)
    "T1" "T2A" "T2B" "T2C" "T3" "T4" "T5"
    ;; 256 glyph encodings (text extended)
    "X2"
    ;; Other encodings
    "LY1" "LV1" "LGR")
  "Package options for the fontenc package.")

(defun LaTeX-fontenc-package-options ()
  "Prompt for package options for the fontenc package."
  (mapconcat 'identity
	     (TeX-completing-read-multiple
	      "Encoding(s): "
	      LaTeX-fontenc-package-options-list) ","))

;;; fontenc.el ends here
