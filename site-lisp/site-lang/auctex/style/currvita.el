;;; currvita.el --- AUCTeX style for `currvita.sty' (v0.9i)

;; Copyright (C) 2015, 2016 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2015-01-05
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

;; This file adds support for `currvita.sty' (v0.9i) from 1999/09/13.
;; `currvita.sty' is part of TeXLive.

;;; Code:

;; This is a modified version of `LaTeX-env-item'.
(defun LaTeX-currvita-env-with-label (env)
  "Insert ENV, a mandatory label and the first item."
  (LaTeX-insert-environment
   env
   (let ((heading (TeX-read-string "Heading of list: ")))
       (format "{%s}" heading)))
  (if (TeX-active-mark)
      (progn
	(LaTeX-find-matching-begin)
	(end-of-line 1))
    (end-of-line 0))
  (delete-char 1)
  (when (looking-at (concat "^[ \t]+$\\|"
			    "^[ \t]*" TeX-comment-start-regexp "+[ \t]*$"))
    (delete-region (point) (line-end-position)))
  (delete-horizontal-space)
  ;; Deactivate the mark here in order to prevent `TeX-parse-macro'
  ;; from swapping point and mark and the \item ending up right after
  ;; \begin{...}.
  (TeX-deactivate-mark)
  (LaTeX-insert-item)
  ;; The inserted \item may have outdented the first line to the
  ;; right.  Fill it, if appropriate.
  (when (and (not (looking-at "$"))
	     (not (assoc env LaTeX-indent-environment-list))
	     (> (- (line-end-position) (line-beginning-position))
		(current-fill-column)))
    (LaTeX-fill-paragraph nil)))


(TeX-add-style-hook
 "currvita"
 (lambda ()

   ;; env's defined by currvita.sty
   (LaTeX-add-environments
    '("cv"      "Heading of CV")
    '("cvlist"  LaTeX-currvita-env-with-label))

   ;; Add "cvlist" to the list of environments which have an optional
   ;; argument for each item
   (add-to-list 'LaTeX-item-list '("cvlist" . LaTeX-item-argument))

   ;; General commands: "\date" is already provided by AUCTeX
   (TeX-add-symbols
    '("cvplace"           t)
    '("cvheadingfont"     0)
    '("cvlistheadingfont" 0)
    '("cvlabelfont"       0)
    '("cvbibname"         0))

   ;; Add new lengths defined by currvita.sty
   (LaTeX-add-lengths "cvlabelwidth" "cvlabelskip" "cvlabelsep"))
 LaTeX-dialect)

(defvar LaTeX-currvita-package-options
  '("LabelsAligned" "TextAligned" "openbib" "ManyBibs" "NoDate")
  "Package options for the currvita package.")

;;; currvita.el ends here
