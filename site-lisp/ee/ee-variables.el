;;; ee-variables.el --- categorized menu of Emacs variables

;; Copyright (C) 2002, 2003, 2004, 2010  Juri Linkov <juri@jurta.org>

;; Author: Juri Linkov <juri@jurta.org>
;; Keywords: ee

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

;;; Code:

(require 'ee)

;;; Constants

(defconst ee-variables-mode-name "ee-variables")

;;; Customizable Variables

(defgroup ee-variables nil
  "Categorized menu of Emacs variables."
  :prefix "ee-variables-"
  :group 'ee)

;;; Data Description

(defvar ee-variables-data
  '[(meta
     (format-version . "0.0.1")
     (view-data-file . "view/variables.ee")
     (collector . ee-variables-data-collect)
     (fields name variable documentation ())
     (key-fields variable))])

;;; Data Extraction

(defun ee-variables-data-collect (data)
  (let* ((field-names (ee-data-field-names data))
         (new-data
          (ee-data-convert-lists-to-vectors
           (let (res)
             (mapatoms (lambda (s)
                         (if (and (symbolp s)
                                  (boundp s)
                                  (not (memq (aref (symbol-name s) 0) '(?: ?*))))
                             (push s res))))
             (mapcar (lambda (s)
                       (mapcar (lambda (field-name)
                                 (cond
                                  ((eq field-name 'name) (symbol-name s))
                                  ((eq field-name 'variable) s)
                                  ((eq field-name 'documentation)
                                   (let ((doc (documentation-property s 'variable-documentation)))
                                     (if (and doc (stringp doc))
                                         (substring doc 0 (string-match "\n" doc)))))
                                  ))
                               field-names))
                     (sort res (lambda (s1 s2)
                                 (string< (symbol-name s1)
                                          (symbol-name s2)))))))))
    (aset new-data 0 (aref data 0))
    new-data))

;;; Actions

(defun ee-variables-call-interactively (&optional arg)
  (interactive)
  (describe-variable (ee-field 'variable)))

;;; Key Bindings

(defvar ee-variables-keymap nil
  "Local keymap for ee-variables mode.")

(defun ee-variables-keymap-make-default ()
  "Defines default key bindings for `ee-variables-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    ;; (define-key map "\C-o" 'ee-variables-call-interactively)
    (setq ee-variables-keymap map)))

(or ee-variables-keymap
    (ee-variables-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-variables (&optional arg)
  "Categorized menu of Emacs variables."
  (interactive "P")
  (ee-view-buffer-create
   (format "*%s*" ee-variables-mode-name)
   ee-variables-mode-name
   ee-variables-keymap
   ee-variables-data))

(provide 'ee-variables)

;;; ee-variables.el ends here
