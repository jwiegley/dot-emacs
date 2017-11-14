;;; commath.el --- AUCTeX style for `commath.sty' (v0.3)

;; Copyright (C) 2016 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2016-07-31
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

;; This file adds support for `commath.sty' (v0.3) from 2006/07/18.
;; `commath.sty' is part of TeXLive.

;;; Code:

(TeX-add-style-hook
 "commath"
 (lambda ()

   ;; Only load amsmath.el, ifthen.el is not necessary
   (TeX-run-style-hooks "amsmath")

   (TeX-add-symbols
    '("dif" 0)
    '("Dif" 0)
    '("od" [ "Order of differentiation" ] "Function" "Variable")
    '("tod" [ "Order of differentiation" ] "Function" "Variable")
    '("dod" [ "Order of differentiation" ] "Function" "Variable")
    '("pd" [ "Order of differentiation" ] "Function" "Variable")
    '("tpd" [ "Order of differentiation" ] "Function" "Variable")
    '("dpd" [ "Order of differentiation" ] "Function" "Variable")
    '("md" 6)
    '("tmd" 6)
    '("dmd" 6)
    '("del" [ "Size argument (0..4)" ] "Argument")
    '("cbr" [ "Size argument (0..4)" ] "Argument")
    '("set" [ "Size argument (0..4)" ] "Argument")
    '("sbr" [ "Size argument (0..4)" ] "Argument")
    '("intoo" [ "Size argument (0..4)" ] "Argument")
    '("intcc" [ "Size argument (0..4)" ] "Argument")
    '("intoc" [ "Size argument (0..4)" ] "Argument")
    '("intco" [ "Size argument (0..4)" ] "Argument")
    '("eval" [ "Size argument (0..4)" ] t)
    '("sVert" [ "Size argument (0..4)" ])
    '("envert" [ "Size argument (0..4)" ] "Argument")
    '("abs" [ "Size argument (0..4)" ] "Argument")
    '("enVert" [ "Size argument (0..4)" ] "Argument")
    '("norm" [ "Size argument (0..4)" ] "Argument")
    '("fullfunction" 5)

    ;; Referencing macros
    '("thmref" TeX-arg-ref)
    '("exref" TeX-arg-ref)
    '("defnref" TeX-arg-ref)
    '("secref" TeX-arg-ref)
    '("lemref" TeX-arg-ref)
    '("propref" TeX-arg-ref)
    '("remref" TeX-arg-ref)
    '("figref" TeX-arg-ref)
    '("colref" TeX-arg-ref)
    '("appref" TeX-arg-ref)
    '("assref" TeX-arg-ref))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("thmref"  "{")
				("exref"   "{")
				("defnref" "{")
				("secref"  "{")
				("lemref"  "{")
				("propref" "{")
				("remref"  "{")
				("figref"  "{")
				("colref"  "{")
				("appref"  "{")
				("assref"  "{"))
			      'reference)))
 LaTeX-dialect)

(defvar LaTeX-commath-package-options nil
  "Package options for the commath package.")

;;; commath.el ends here
