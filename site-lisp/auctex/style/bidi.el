;;; bidi.el --- AUCTeX style for the (XeLaTeX) bidi package

;; Copyright (C) 2016 Free Software Foundation, Inc.

;; Author: Uwe Brauer <oub@mat.ucm.es>
;; Created: 2016-03-06
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

;; This file adds support for the bidi package.

;;; Code:

(defvar LaTeX-bidi-package-options '("RTLdocument" "rldocument")
  "Package options for the bidi package.")

(TeX-add-style-hook
 "bidi"
 (lambda ()
   (TeX-check-engine-add-engines 'xetex)
   (LaTeX-add-environments
    "LTR"
    "RTL")
   ;; Fontification
   (TeX-add-symbols
    '("setRL" 0)
    '("unsetRL" 0)
    '("setRTL" 0)
    '("unsetRTL" 0)
    '("setLR" 0)
    '("unsetLR" 0)
    '("setLTR" 0)
    '("unsetLTR" 0)
    '("LR" 1)
    '("LRE" 1)
    '("RLE" 1)
    '("RL" 1)))
 LaTeX-dialect)


;;; bidi.el ends here
