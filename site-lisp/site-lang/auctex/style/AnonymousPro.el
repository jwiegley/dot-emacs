;;; AnonymousPro.el --- AUCTeX style for `AnonymousPro.sty' (v2.1)

;; Copyright (C) 2014 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2014-10-30
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

;; This file adds support for `AnonymousPro.sty' (v2.1) from
;; 2014/03/22.  `AnonymousPro.sty' is part of TeXLive.

;;; Code:

(TeX-add-style-hook
 "AnonymousPro"
 (lambda ()

   ;; Run style hook for textcomp
   (TeX-run-style-hooks "textcomp")

   ;; New symbols
   (TeX-add-symbols
    "ANPapplelogo"
    "ANPappleopen"
    "ANPapproxequal"
    "ANPback"
    "ANPblackdiamond"
    "ANPcheckmark"
    "ANPcopy"
    "ANPellipsis"
    "ANPendtab"
    "ANPerasetotheright"
    "ANPgreaterequal"
    "ANPHbar"
    "ANPhbar"
    "ANPinfinity"
    "ANPinsert"
    "ANPintegral"
    "ANPlessequal"
    "ANPlozenge"
    "ANPnotequal"
    "ANPoptionkey"
    "ANPpartialdiff"
    "ANPPi"
    "ANPpi"
    "ANPproduct"
    "ANPshift"
    "ANPshiftlock"
    "ANPSigma"
    "ANPsigma"
    "ANPsigmaone"
    "ANPsummation"
    "ANPtab"
    "ANPReturnSign"
    "ANPShoulderedOpenBox"
    "ANPUpArrowHead"
    "ANPInsertSign"
    "ANPUpArrowHeadBars"
    "ANPHelm"
    "ANPOpenBox"
    "ANPDelta"
    "ANPverticaltab"
    "ANPNumeroSign"))
 LaTeX-dialect)

(defvar LaTeX-AnonymousPro-package-options
  '("ttdefault" "scale")
  "Package options for the AnonymousPro package.")

;;; AnonymousPro.el ends here
