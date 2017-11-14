;;; tabularx.el --- AUCTeX style for the tabularx package.

;; Copyright (C) 2009, 2013-2016 Free Software Foundation, Inc.

;; Author: Ralf Angeli <angeli@caeruleus.net>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2009-02-22
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

;; This file adds support for the tabularx package.

;;; Code:

(defvar LaTeX-tabularx-package-options
  '("infoshow" "debugshow")
  "Package options for the tabularx package.")

(TeX-add-style-hook
 "tabularx"
 (lambda ()
   ;; Make tabularx the default tabular environment
   (setq LaTeX-default-tabular-environment "tabularx")
   ;; Use the enhanced tabular indentation.  Append to
   ;; `LaTeX-indent-environment-list' in order not to override custom settings.
   (add-to-list (make-local-variable 'LaTeX-indent-environment-list)
		'("tabularx" LaTeX-indent-tabular) t)

   ;; Append tabularx to `LaTeX-item-list' with `LaTeX-item-tabular*'
   (add-to-list 'LaTeX-item-list '("tabularx" . LaTeX-item-tabular*) t)

   ;; New symbols
   (TeX-add-symbols
    "tracingtabularx"
    '("tabularxcolumn" 0))
   ;; New environments
   (LaTeX-add-environments
    ;; XXX: The tabularx environment takes the same arguments as the
    ;; tabular* environment.  However, the supported tokens in the
    ;; format can differ, so at some point in time we might want to
    ;; separate tabular* and tabularx.
    '("tabularx" LaTeX-env-tabular*))
   
   ;; `tabularx' requires array to define the column types
   (TeX-run-style-hooks "array")

   ;; `tabularx.sty' adds one new column specification letter.
   (set (make-local-variable 'LaTeX-array-column-letters)
	(concat LaTeX-array-column-letters "X")))
 LaTeX-dialect)

;;; tabularx.el ends here
