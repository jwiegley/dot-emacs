;;; ee-views.el --- display, edit and switch views

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

(defconst ee-views-mode-name "ee-views")

;;; Customizable Variables

(defgroup ee-views nil
  "Display, edit and switch views."
  :group 'ee)

;;; Data Description

;; This data structure is dummy and not used at all, because when
;; ee-views is called, it is replaced by views from parent buffer
(defvar ee-views-data
  '[(meta
     (format-version . "0.0.1")
     (data-file . "view/views.ee")
     (view-data-file . "view/views.ee")
     (collector . ee-views-data-collect)
     (fields ;type name category default r-filter c-tree-builder r-tree-builder c-path-finder c-sorter r-sorter c-calculator r-calculator c-title-printer r-title-printer c-printer r-printer post-generate post-update r-select r-execute
             ())
     (key-fields name))])

;;; Data Extraction

(defun ee-views-data-collect (data)
  (with-current-buffer ee-parent-buffer
    ee-view-data))

;;; Actions

(defun ee-views-switch-to-buffer (&optional arg)
  (interactive)
  (let ((setters (ee-data-meta-setters-get-set ee-data)))
    ;; Change default view
    (ee-data-records-do
     ee-data
     (lambda (r i)
       (ee-data-field-set 'default nil r setters)))
    (ee-data-field-set 'default t (ee-view-record-get) setters))
  (switch-to-buffer ee-parent-buffer)
  (let ((data-getters (ee-data-meta-getters-get-set ee-data)))
    (ee-view-buffer-update)))

;;; Key Bindings

(defvar ee-views-keymap nil
  "Local keymap for ee-views mode.")

(defun ee-views-keymap-make-default ()
  "Defines default key bindings for `ee-views-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    ;; (define-key map "\C-o" 'ee-views-select)
    (setq ee-views-keymap map)))

(or ee-views-keymap
    (ee-views-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-views (&optional arg)
  "Display, edit and switch views."
  (interactive "P")
  (if (eq major-mode 'ee-mode)
      (ee-view-buffer-create
       (format "*%s*/%s" ee-views-mode-name (buffer-name))
       ee-views-mode-name
       ee-views-keymap
       ee-views-data
       nil
       nil
       t)
    (error "Command ee-views can be invoked only on ee buffers")))

(provide 'ee-views)

;;; ee-views.el ends here
