;;; ltablex.el --- AUCTeX style for `ltablex.sty' (v1.1)

;; Copyright (C) 2015 Free Software Foundation, Inc.

;; Author: Arash Esbati <esbati'at'gmx.de>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2015-03-14
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

;; This file adds support for `ltablex.sty' (v1.1) from 2014/08/13.
;; `ltablex.sty' is part of TeXLive.  `ltablex.sty' modifies the
;; tabularx environment to combine the features of the tabularx
;; package with those of the longtable package.  All we need is to
;; call those styles and add two macros.

;;; Code:

(TeX-add-style-hook
 "ltablex"
 (lambda ()
   (TeX-run-style-hooks "tabularx" "longtable")
   (TeX-add-symbols
    '("keepXColumns" 0)
    '("convertXColumns" 0)))
 LaTeX-dialect)

(defvar LaTeX-ltablex-package-options nil
  "Package options for the ltablex package.")

;;; ltablex.el ends here
