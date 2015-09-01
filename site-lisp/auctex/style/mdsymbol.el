;;; mdsymbol.el --- AUCTeX style for `mdsymbol.sty' (v0.5)

;; Copyright (C) 2014 Free Software Foundation, Inc.

;; Author: Arash Esbati <esbati'at'gmx.de>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2014-10-25
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

;; This file adds support for `mdsymbol.sty' (v0.5) from 2012/11/18.
;; The latest version of is available from <https://www.github.com/sebschub>.
;; `mdsymbol.sty' is part of TeXLive.

;;; Code:

(TeX-add-style-hook
 "mdsymbol"
 (lambda ()

   ;; Run style hook for various packages loaded by mdsymbol
   (TeX-run-style-hooks "textcomp" "amsmath")

   ;; New symbols
   (TeX-add-symbols

    ;; These macros take one argument; we follow latex.el and use the
    ;; t specifier for the argument; over- and underbrace and sqrt are
    ;; already available
    '("overgroup"  t)
    '("undergroup" t)
    '("overlinesegment"  t)
    '("overleftharpoon"  t)
    '("overrightharpoon" t)
    '("underlinesegment" t)
    ;;
    '("widehat"       t)
    '("widetilde"     t)
    '("wideparen"     t)
    '("vec"           t)
    '("middlebar"     t)
    '("middleslash"   t)
    '("strokethrough" t)
    ;;
    '("overlining"    t))

   ;; The following macros are usually defined, since retainmissing
   ;; defaults to false
   (unless (or (LaTeX-provided-package-options-member "mdsymbol" "retainmissing=true")
               (LaTeX-provided-package-options-member "mdsymbol" "retainmissing"))
     (TeX-add-symbols
      '("dagger")
      '("ddagger")
      '("mathparagraph")
      '("mathsection")
      '("mathdollar")
      '("mathsterling")
      '("yen")
      '("hbar")
      '("hslash")
      '("circledR")
      '("circledS")
      '("lambdabar")
      '("lambdaslash"))))
 LaTeX-dialect)

(defvar LaTeX-mdsymbol-package-options
  '(;;
    ("normalweight"  ("Light" "Regular" "autolight" "autoregular"))
    ("boldweight"    ("Semibold" "Bold" "autosemibold"))
    ("onlysansmath"  ("true" "false"))
    ("retainmissing" ("true" "false"))
    ("scale")
    ("largedelims"   ("true" "false")))
  "Package options for the mdsymbol package.")

(defun LaTeX-mdsymbol-package-options nil
  "Prompt for package options for the mdsymbol package."
  (TeX-read-key-val t LaTeX-mdsymbol-package-options))

;;; mdsymbol.el ends here
