;;; ee-fields.el --- display and edit fields of the current record

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

(defconst ee-fields-mode-name "ee-fields")

;;; Customizable Variables

(defgroup ee-fields nil
  "Display and edit fields of the current record."
  :group 'ee)

;;; Data Description

(defvar ee-fields-data
  '[(meta
     (format-version . "0.0.1")
     (view-data-file . "view/fields.ee")
     (collector . ee-fields-data-collect)
     (fields name value)
     (key-fields name))])

;;; Data Extraction

(defun ee-fields-data-collect (data)
  (with-current-buffer ee-parent-buffer
    (let* ((record (ee-view-record-get))
           (field-names (ee-data-field-names ee-data record))
           (getters (ee-data-meta-getters-get-set ee-data))
           (new-data
            (ee-data-convert-lists-to-vectors
             (mapcar
              (lambda (field-name)
                (list
                 field-name
                 (ee-data-field-get field-name record getters)))
              field-names))))
      (aset new-data 0 (aref data 0))
      new-data)))

;;; Actions

;; TODO: make function to read from separate buffer as in Gnus format, C-c C-c
;; (if (or (consp value) (and (stringp value) (string-match "\n" value)))
;;     (create-buffer (pp value)))
(defun ee-fields-edit-field-in-buffer (&optional arg)
  (interactive)
  ;; TODO: instead of gnus-edit-form make generic functions and modes
  ;; for editing strings and sexps in the separate buffers
  (gnus-edit-form (ee-field 'value) "documentation" 'ee-fields-edit-field-in-buffer-done))

(defun ee-fields-edit-field-in-buffer-done (new-value &optional arg)
  (interactive)
  (let* ((r (ee-view-record-get))
         (data-getters (ee-data-meta-getters-get-set ee-data))
         (name (ee-data-field-get 'name r data-getters)))
    (with-current-buffer ee-parent-buffer
      (let ((data-setters (ee-data-meta-setters-get-set ee-data)))
        (ee-data-field-set name new-value (ee-view-record-get) data-setters)
        (ee-view-buffer-update)))
    (ee-view-buffer-update t)))

(defun ee-fields-edit-field-in-minibuffer (&optional arg)
  (interactive)
  (let* ((r (ee-view-record-get))
         (data-getters (ee-data-meta-getters-get-set ee-data))
         (name (ee-field 'name r data-getters))
         (value (ee-field 'value r data-getters))
         (new-value
          (read-from-minibuffer (format "%s: " name)
                                (format "%S" value) ;(pp-to-string value)
                                nil t)))
    (with-current-buffer ee-parent-buffer
      (let ((data-setters (ee-data-meta-setters-get-set ee-data)))
        (ee-data-field-set name new-value (ee-view-record-get) data-setters)
        (ee-view-buffer-update)))
    (ee-view-buffer-update t)))

;;; Key Bindings

(defvar ee-fields-keymap nil
  "Local keymap for ee-fields mode.")

(defun ee-fields-keymap-make-default ()
  "Defines default key bindings for `ee-fields-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    ;; (define-key map "\C-o" 'ee-fields-select)
    (setq ee-fields-keymap map)))

(or ee-fields-keymap
    (ee-fields-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-fields (&optional arg)
  "Display and edit fields of the current record."
  (interactive "P")
  (if (eq major-mode 'ee-mode)
      (ee-view-buffer-create
       (format "*%s*/%s" ee-fields-mode-name (buffer-name))
       ee-fields-mode-name
       ee-fields-keymap
       ee-fields-data
       nil
       nil
       t ;; needed to reread?
       )
    (error "Command ee-fields can be invoked only on ee buffers")))

(provide 'ee-fields)

;;; ee-fields.el ends here
