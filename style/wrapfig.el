;;; wrapfig.el --- AUCTeX style for `wrapfig.sty' version v3.6

;; Copyright (C) 2014 Free Software Foundation, Inc.

;; Author: Arash Esbati <esbati'at'gmx.de>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2014-12-13
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

;; This file adds support for `wrapfig.sty' version v3.6 from
;; 2003/01/31.  `wrapfig.sty' is part of TeXLive.

;;; Code:

(TeX-add-style-hook
 "wrapfig"
 (lambda ()
   (LaTeX-add-environments
    ;; \begin{wrapfigure}[No.lines]{Placement}[Overhang]{Width} ... \end{wrapfigure}
    '("wrapfigure"
      (lambda (env &rest ignore)
	(LaTeX-insert-environment
	 env
	 (let ((narrow    (TeX-read-string "(Optional) Number of narrow lines: "))
	       (placement (completing-read
			   "Placement: " '(("r") ("R")
					   ("l") ("L")
					   ("i") ("I")
					   ("o") ("O"))))
	       (overhang  (TeX-read-string "(Optional) Overhang: "))
	       (width     (TeX-read-string "Width: ")))
	   (concat
	    (unless (string= narrow "")
	      (format "[%s]" narrow))
	    (format "{%s}" placement)
	    (unless (string= overhang "")
	      (format "[%s]" overhang))
	    (format "{%s}" width))))))
    ;;
    ;; \begin{wraptable}[No.lines]{Placement}[Overhang]{Width} ... \end{wraptable}
    '("wraptable"
      (lambda (env &rest ignore)
	(LaTeX-insert-environment
	 env
	 (let ((narrow    (TeX-read-string "(Optional) Number of narrow lines: "))
	       (placement (completing-read
			   "Placement: " '(("r") ("R")
					   ("l") ("L")
					   ("i") ("I")
					   ("o") ("O"))))
	       (overhang  (TeX-read-string "(Optional) Overhang: "))
	       (width     (TeX-read-string "Width: ")))
	   (concat
	    (unless (string= narrow "")
	      (format "[%s]" narrow))
	    (format "{%s}" placement)
	    (unless (string= overhang "")
	      (format "[%s]" overhang))
	    (format "{%s}" width))))))
    ;;
    ;; \begin{wrapfloat}{<Type>}[No.lines]{Placement}[Overhang]{Width} ... \end{wrapfloat}
    '("wrapfloat"
      (lambda (env &rest ignore)
	(LaTeX-insert-environment
	 env
	 (let ((floattype (TeX-read-string "Float type: "))
	       (narrow    (TeX-read-string "(Optional) Number of narrow lines: "))
	       (placement (completing-read
			   "Placement: " '(("r") ("R")
					   ("l") ("L")
					   ("i") ("I")
					   ("o") ("O"))))
	       (overhang  (TeX-read-string "(Optional) Overhang: "))
	       (width     (TeX-read-string "Width: ")))
	   (concat
	    (format "{%s}" floattype)
	    (unless (string= narrow "")
	      (format "[%s]" narrow))
	    (format "{%s}" placement)
	    (unless (string= overhang "")
	      (format "[%s]" overhang))
	    (format "{%s}" width))))))))
 LaTeX-dialect)

(defvar LaTeX-wrapfig-package-options '("verbose")
  "Package options for the wrapfig package.")

;;; wrapfig.el ends here
