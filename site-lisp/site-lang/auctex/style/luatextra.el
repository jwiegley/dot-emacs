;;; luatextra.el --- AUCTeX style for `luatextra.sty' version 1.0.

;; Copyright (C) 2014 Free Software Foundation, Inc.

;; Author: Davide G. M. Salvetti <salve@debian.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2014-11-15
;; Keywords: tex

;; This file is part of AUCTeX.

;; AUCTeX is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by the
;; Free Software Foundation; either version 3, or (at your option) any
;; later version.

;; AUCTeX is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
;; for more details.

;; You should have received a copy of the GNU General Public License
;; along with AUCTeX; see the file COPYING.  If not, see
;; <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This file adds support for `luatextra.sty' 1.0.

;;; Code:

(TeX-add-style-hook
    "luatextra"
  (lambda ()
    (TeX-run-style-hooks "ifluatex" "fontspec"
			 ;; FIXME: yet to be written:
			 ;; "luatexbase"
			 "metalogo" "luacode"))
  LaTeX-dialect)

(defvar LaTeX-luatextra-package-options nil
  "Package options for the ifluatex package.")

;;; luatextra.el ends here
