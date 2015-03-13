;;; ee-customize.el --- browse Emacs customization groups

;; Copyright (C) 2002, 2003, 2004, 2010  Juri Linkov <juri@jurta.org>

;; Author: Juri Linkov <juri@jurta.org>
;; Keywords: ee, customize

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

(defconst ee-customize-mode-name "ee-customize")

;;; Customizable Variables

(defgroup ee-customize nil
  "Browse Emacs customization groups."
  :prefix "ee-customize-"
  :group 'ee)

(defcustom ee-customize-root-group 'emacs
  "Root group name."
  :type 'symbol
  :group 'ee-customize)

;;; Data Description

(defvar ee-customize-data
  '[(meta
     (format-version . "0.0.1")
     (view-data-file . "view/customize.ee")
     (collector . ee-customize-data-collect)
     (fields name type parent-group ())
     (key-fields name))])

;;; Data Extraction

(defun ee-customize-data-collect (data)
  (let ((new-data (ee-data-convert-lists-to-vectors
                   (ee-customize-data-collect-groups
                    (ee-data-field-names data)
                    ee-customize-root-group))))
    (aset new-data 0 (aref data 0))
    new-data))

(defun ee-customize-data-collect-groups (field-names parent-group)
  (mapcan (lambda (item)
            (append (if (eq (cadr item) 'custom-group)
                        (list
                         (mapcar (lambda (field-name)
                                   (cond
                                    ((eq field-name 'name) (car item))
                                    ((eq field-name 'type) (cadr item))
                                    ((eq field-name 'parent-group) parent-group)))
                                 field-names)))
                    (if (and (eq (cadr item) 'custom-group)
                             (not (eq (car item) parent-group)))
                        (ee-customize-data-collect-groups field-names (car item)))))
          (get parent-group 'custom-group)))

;;; Actions

(defun ee-customize-customize-group (&optional arg)
  (interactive)
  (customize-group (ee-field 'name)))

;;; Key Bindings

(defvar ee-customize-keymap nil
  "Local keymap for ee-customize mode.")

(defun ee-customize-keymap-make-default ()
  "Defines default key bindings for `ee-customize-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    (define-key map "\C-o" 'ee-customize-customize-group)
    (setq ee-customize-keymap map)))

(or ee-customize-keymap
    (ee-customize-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-customize (&optional arg)
  "Browse Emacs customization groups."
  (interactive "P")
  (require 'cus-edit)
  (ee-view-buffer-create
   (format "*%s*" ee-customize-mode-name)
   ee-customize-mode-name
   ee-customize-keymap
   ee-customize-data))

(provide 'ee-customize)

;;; ee-customize.el ends here
