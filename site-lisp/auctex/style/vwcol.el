;;; vwcol.el --- AUCTeX style for `vwcol.sty' (v0.2)

;; Copyright (C) 2015 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2015-07-04
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

;; This file adds support for `vwcol.sty' (v0.2) from 2015/02/10.
;; `vwcol.sty' is part of TeXLive.

;;; Code:

(defvar LaTeX-vwcol-key-val-options
  '(("widths")
    ("sep"       ("fill"))
    ("presep"    ("true" "false"))
    ("postsep"   ("true" "false"))
    ("sidesep"   ("true" "false"))
    ("rule"      ("none" "0pt"))
    ("prerule"   ("true" "false"))
    ("postrule"  ("true" "false"))
    ("siderule"  ("true" "false"))
    ("justify"   ("ragged" "flush" "raggedleft" "center"))
    ("rulecolor")
    ("indent")
    ("lines"))
  "Key=value options for vwcol macros and environments.")

(TeX-add-style-hook
 "vwcol"
 (lambda ()

   (LaTeX-add-environments
    '("vwcol" LaTeX-env-args
      [ TeX-arg-key-val LaTeX-vwcol-key-val-options ]))

   (TeX-add-symbols
    '("vwcolsetup" (TeX-arg-key-val LaTeX-vwcol-key-val-options)))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("vwcolsetup" "{"))
			      'function)))
 LaTeX-dialect)

(defvar LaTeX-vwcol-package-options '("quiet")
  "Package options for the vwcol package.")

;;; vwcol.el ends here
