;;; ifluatex.el --- AUCTeX style for `ifluatex.sty' version 1.3.

;; Copyright (C) 2014, 2016 Free Software Foundation, Inc.

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

;; This file adds support for `ifluatex.sty' 1.3.

;;; Code:

(defun LaTeX-ifluatex-set-exit-mark (optional)
  "Discard OPTIONAL and set exit-mark to current point."
  (set-marker exit-mark (point)))

(TeX-add-style-hook
    "ifluatex"
  (lambda ()
    (TeX-add-symbols
     '("ifluatex"
       (TeX-arg-literal "%\n")
       LaTeX-ifluatex-set-exit-mark
       (TeX-arg-literal "\n\\else%\n\\fi%"))
     '("luatexversion" 0)
     '("luatexrevision" 0))
    (TeX-declare-expert-macros
     "ifluatex"
     "ifluatex" "luatexversion" "luatexrevision")

    ;; This package is used to make it possible to compile a document with both
    ;; LuaTeX and base TeX engines.  By setting `TeX-check-engine-list' to nil
    ;; we ignore engine restrictions posed by other packages.
    (setq TeX-check-engine-list nil)

    (when (and (featurep 'font-latex)
	       (eq TeX-install-font-lock 'font-latex-setup))
      (font-latex-add-keywords '(("luatexversion")
				 ("luatexrevision"))
			       'function)))
  LaTeX-dialect)

(defvar LaTeX-ifluatex-package-options nil
  "Package options for the ifluatex package.")

;;; ifluatex.el ends here
