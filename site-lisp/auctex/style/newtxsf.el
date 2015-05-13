;;; newtxsf.el --- AUCTeX style for `newtxsf.sty' (v1.0)

;; Copyright (C) 2014 Free Software Foundation, Inc.

;; Author: Arash Esbati <esbati'at'gmx.de>
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

;; This file adds support for `newtxsf.sty' (v1.0) from 2014/11/14.
;; `newtxsf.sty' is part of TeXLive.

;;; Code:

(TeX-add-style-hook
 "newtxsf"
 (lambda ()
   ;; Run style hook for amsmath
   (TeX-run-style-hooks "amsmath")

   ;; New symbols
   (TeX-add-symbols
    '("upimath"  0)
    '("upjmath"  0)))
 LaTeX-dialect)

(defvar LaTeX-newtxsf-package-options
  '("scaled"
    "nosymbolsc"
    "cmintegrals"
    "amssymbols"
    "noamssymbols"
    "uprightGreek"
    "slantedGreek"
    "frenchmath")
  "Package options for the newtxsf package.")

;;; newtxsf.el ends here
