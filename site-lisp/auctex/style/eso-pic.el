;;; eso-pic.el --- AUCTeX style for `eso-pic.sty' (v2.0d)

;; Copyright (C) 2014 Free Software Foundation, Inc.

;; Author: Arash Esbati <esbati'at'gmx.de>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2014-10-29
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

;; This file adds support for `eso-pic.sty' (v2.0d) from 2013/10/06.
;; `eso-pic.sty' is part of TeXLive.

;;; Code:

(TeX-add-style-hook
 "eso-pic"
 (lambda ()

   ;; Run style hook for eso-pic
   (TeX-run-style-hooks "atbegshi")

   ;; New symbols
   (TeX-add-symbols

    ;; Basic commands
    '("AddToShipoutPictureBG"   t)
    '("AddToShipoutPictureBG*"  t)
    '("AddToShipoutPictureFG"   t)
    '("AddToShipoutPictureFG*"  t)
    '("ClearShipoutPictureBG"   0)
    '("ClearShipoutPictureFG"   0)

    ;; Helper macros
    '("AtPageUpperLeft"         t)
    '("AtPageLowerLeft"         t)
    '("AtPageCenter"            t)
    '("AtTextUpperLeft"         t)
    '("AtTextLowerLeft"         t)
    '("AtTextCenter"            t)
    '("AtStockUpperLeft"        t)
    '("AtStockLowerLeft"        t)
    '("AtStockCenter"           t)

    ;; Aux. commands
    '("LenToUnit"               t)
    '("gridSetup"
      [ "Grid unit name" ]  "Grid unit"    "Label factor"
      "Grid delta"          "Grid Delta"   "Gap"))

   ;; Declare expert macro
   (TeX-declare-expert-macros
    "eso-pic"
    "gridSetup" "LenToUnit"))
 LaTeX-dialect)

(defvar LaTeX-eso-pic-package-options
  '(;;
    ("pscoord"      ("true" "false"))
    ("texcoord"     ("true" "false"))
    ("grid"         ("true" "false"))
    ("gridunit"     ("mm" "in" "bp" "pt"))
    ("gridcolor")
    ("subgridcolor")
    ("subgridstyle" ("solid" "dotted"))
    ("dvips"        ("true" "false")))
  "Package options for the eso-pic package.")

(defun LaTeX-eso-pic-package-options nil
  "Prompt for package options for the eso-pic package."
  (TeX-read-key-val t LaTeX-eso-pic-package-options))

;;; eso-pic.el ends here
