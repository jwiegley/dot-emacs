;;; subfiles.el --- AUCTeX style for the subfiles package.

;; Copyright (C) 2016 Free Software Foundation, Inc.

;; Author: Uwe Brauer <oub@mat.ucm.es>
;; Created: 07 Nov 2016
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

;; Acknowledgements
;; Mosè Giordano <mose@gnu.org>
;; Arash Esbati <arash@gnu.org>

;;; Commentary:

;; This file adds support for the subfiles package.

;;; Code:

(defvar LaTeX-subfiles-package-options nil
  "Package options for the subfiles package.")

(defun LaTeX-subfiles-class-options ()
  "Return name of the main file relative to current subfile."
  (file-relative-name
   (read-file-name
    "Main file: " nil nil nil nil
    (lambda (texfiles)
      (string-match "\\.tex$" texfiles)))
   (TeX-master-directory)))

(TeX-add-style-hook
 "subfiles"
 (lambda ()

   ;; The following code will run `TeX-run-style-hooks' on the subfile
   ;; master file.  Thanks to Mosè Giordano <mose@gnu.org> for
   ;; presenting a better solution using `assoc'.
   (let ((master-file (cadr (assoc "subfiles" LaTeX-provided-class-options))))
     (when (stringp master-file)
       (TeX-run-style-hooks
	(file-name-sans-extension master-file))))

   (TeX-add-symbols
    '("subfile" TeX-arg-file))

   ;; Ensure that \subfile stays in one line
   (LaTeX-paragraph-commands-add-locally "subfile")

   ;; Tell AUCTeX that \subfile loads a file.  regexp is the same as
   ;; for \input or \include.  This will run `TeX-run-style-hooks' on
   ;; subfile(s) when master file is loaded.
   (TeX-auto-add-regexp
    `(,(concat
	"\\\\subfile"
	"{\\(\\.*[^#}%\\\\\\.\n\r]+\\)\\(\\.[^#}%\\\\\\.\n\r]+\\)?}")
      1 TeX-auto-file))

   ;; Tell RefTeX the same thing.
   (when (and (boundp 'reftex-include-file-commands)
	      (not (member "subfile" reftex-include-file-commands)))
     (add-to-list 'reftex-include-file-commands "subfile" t)
     (reftex-compile-variables))

   ;; The following code will fontify `\subfile{}' like \input.
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("subfile" "{"))
			      'reference)))
 LaTeX-dialect)

;;; subfiles.el ends here
