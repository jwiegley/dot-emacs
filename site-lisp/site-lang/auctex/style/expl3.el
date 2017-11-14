;;; expl3.el --- AUCTeX style for `expl3.sty'

;; Copyright (C) 2015, 2017 Free Software Foundation, Inc.

;; Author: Tassilo Horn <tsdh@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2015-02-22
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

;; This file adds support for `expl3.sty'.

;;; Code:

(defvar LaTeX-expl3-syntax-table
  (let ((st (copy-syntax-table LaTeX-mode-syntax-table)))
    ;; Make _ and : symbol chars
    (modify-syntax-entry ?\_ "_" st)
    (modify-syntax-entry ?\: "_" st)
    st))

(TeX-add-style-hook
 "expl3"
 (lambda ()
   (set-syntax-table LaTeX-expl3-syntax-table)
   (when (and (fboundp 'font-latex-update-font-lock)
	      (eq TeX-install-font-lock 'font-latex-setup))
     ;; Tell font-lock about the update.
     (font-latex-update-font-lock t)))
 LaTeX-dialect)

(defun LaTeX-expl3-package-options ()
  "Read the expl3 package options from the user."
  (TeX-read-key-val t '(("check-declarations" ("true" "false"))
			("log-functions" ("true" "false"))
			("driver" ("auto"    "latex2e"
				   "dvips"   "dvipdfmx"
				   "pdfmode" "xdvipdfmx")))))

;;; expl3.el ends here
