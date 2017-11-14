;;; zlmtt.el --- AUCTeX style for `zlmtt.sty' (v1.01)

;; Copyright (C) 2014 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2014-10-31
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

;; This file adds support for `zlmtt.sty' (v1.01) from 2014/06/28.
;; `zlmtt.sty' is part of TeXLive.

;;; Code:

(TeX-add-style-hook
 "zlmtt"
 (lambda ()

   ;; New symbols
   (TeX-add-symbols
    '("proptt" t)   ; proportional typewriter
    '("monott" t)   ; monospace typewriter
    '("lctt"   t))  ; light condensed typewriter

   ;; Fontification
   (when (and (featurep 'font-latex)
              (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("proptt"   "{")
                                ("monott"   "{")
                                ("lctt"     "{"))
                              'type-command)))
 LaTeX-dialect)

(defvar LaTeX-zlmtt-package-options
  '("light" "l" "lightcondensed" "lc" "med" "m"
    "proportional" "p" "scaled")
  "Package options for the zlmtt package.")

;;; zlmtt.el ends here
