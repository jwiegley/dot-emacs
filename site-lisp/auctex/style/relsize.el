;;; relsize.el --- AUCTeX style for `relsize.sty' version v4.1

;; Copyright (C) 2014 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2014-12-14
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

;; This file adds support for `relsize.sty' version v4.1 from
;; 2013/03/29.  `relsize.sty' is part of TeXLive.

;;; Code:

(TeX-add-style-hook
 "relsize"
 (lambda ()
   (TeX-add-symbols
    ;; Declarations and commands
    '("relsize"     "Steps"                    )
    '("relscale"    "Scale factor"             )
    '("larger"      [ "Steps (default: 1)" ] -1)
    '("smaller"     [ "Steps (default: 1)" ] -1)
    '("textlarger"  [ "Steps" ]               t)
    '("textsmaller" [ "Steps" ]               t)
    '("textscale"   "Scale factor"            t)
    '("mathlarger"                            t)
    '("mathsmaller"                           t))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     ;; This is not easy, are the first 2 'variable oder rather
     ;; 'type-declaration?  I start with 'type-declaration, let the
     ;; users decide
     (font-latex-add-keywords '(("relsize"            "")
				("relscale"           "")
				("larger"             "")
				("smaller"            ""))
			      'type-declaration)
     (font-latex-add-keywords '(("textlarger"         "[{")
				("textsmaller"        "[{")
				("textscale"          "{{"))
			      'type-command)))
 LaTeX-dialect)

(defvar LaTeX-relsize-package-options nil
  "Package options for the relsize package.")

;;; relsize.el ends here
