;;; amsfonts.el --- AUCTeX style for `amsfonts.sty' version 3.01

;; Copyright (C) 2016 Free Software Foundation, Inc.

;; Maintainer: auctex-devel@gnu.org
;; Author: Mosè Giordano <mose@gnu.org>
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

;; This file adds support for `amsfonts.sty' version 3.01.

;;; Code:

(TeX-add-style-hook
 "amsfonts"
 (lambda ()
   (TeX-add-symbols
    '("bold" 1))
   ;; New math font by `amsfonts'.
   (setq TeX-font-list
	 (append
	  TeX-font-list
	  '((?\C-k "" "" "\\mathfrak{" "}"))))
   ;; Fontification
   (when (and (featurep 'font-latex)
   	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("bold" "{"))
			      'bold-command)))
 LaTeX-dialect)

;; The `psamsfonts' option is obsolete in AMSFonts v3
(defvar LaTeX-amsfonts-package-options nil
  "Package options for the amsfonts package.")

;;; amsfonts.el ends here.
