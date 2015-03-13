;;; ee-finder.el --- keyword-based Emacs code finder

;; Copyright (C) 2002, 2003, 2004, 2010  Juri Linkov <juri@jurta.org>

;; Author: Juri Linkov <juri@jurta.org>
;; Keywords: ee, help

;; This file is [not yet] part of GNU Emacs.

;; This package is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This package is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this package; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; See the file README and documentation for more information.

;; TODO: fix the function `finder-compile-keywords':
;; replace (subst-char-in-region keystart (point) ?, ? )
;; by code that correctly splits the keywords:
;; 1. if keywords string has comma, then split string by comma,
;; 2. if keywords string has no comma, then split string by space
;; so convert e.g.
;; "Keywords: multibyte character, character set, syntax, category"
;; to ("multibyte character" "character set" "syntax" "category")
;; instead of ("multibyte" "character" "character" "set" "syntax" "category")
;; and
;; "Keywords: dired extensions files"
;; to ("dired" "extensions" "files")

;; TODO: collect other fields from lisp files (qv lisp-mnt.el)

;;; Code:

(require 'ee)

(eval-when-compile
  (require 'finder))

;;; Constants

(defconst ee-finder-mode-name "ee-finder")

;;; Customizable Variables

(defgroup ee-finder nil
  "Keyword-based Emacs code finder."
  :prefix "ee-finder-"
  :group 'ee)

;;; Data Description

(defvar ee-finder-data
  '[(meta
     (format-version . "0.0.1")
     (database-version . "0.0.1")
     (view-data-file . "view/finder.ee")
     (collector . ee-finder-data-collect)
     (fields file synopsis keywords ())
     (key-fields file))])

;;; Data Extraction

(defun ee-finder-data-collect (data)
  (let* ((field-names (ee-data-field-names data))
         (new-data
          (ee-data-convert-lists-to-vectors
           (mapcar
            (lambda (package)
              (mapcar
               (lambda (field-name)
                 (cond
                  ((eq field-name 'file)     (nth 0 package))
                  ((eq field-name 'synopsis) (nth 1 package))
                  ((eq field-name 'keywords) (nth 2 package))))
               field-names))
            finder-package-info))))
    (aset new-data 0 (aref data 0))
    new-data))

;;; Actions

(defun ee-finder-select (&optional arg other-window)
  (interactive)
  ;; TODO: find file
  (find-file (locate-library (ee-field 'file))))

(defun ee-finder-commentary (&optional arg other-window)
  "Display FILE's commentary section."
  (interactive)
  (finder-commentary (ee-field 'file)))

;;; Key Bindings

(defvar ee-finder-keymap nil
  "Local keymap for ee-finder mode.")

(defun ee-finder-keymap-make-default ()
  "Defines default key bindings for `ee-finder-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    (define-key map "i" 'ee-finder-commentary)
    ;; (define-key map "o" 'ee-finder-switch-to-buffer-other-window)
    ;; (define-key map "\C-o" 'ee-finder-display-buffer)
    (setq ee-finder-keymap map)))

(or ee-finder-keymap
    (ee-finder-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-finder (&optional arg)
  "Keyword-based Emacs code finder."
  (interactive "P")
  (require 'finder)
  (ee-view-buffer-create
   (format "*%s*" ee-finder-mode-name)
   ee-finder-mode-name
   ee-finder-keymap
   ee-finder-data))

(provide 'ee-finder)

;;; ee-finder.el ends here
