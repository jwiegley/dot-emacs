;;; ee-example.el --- accompanying example for demonstration of ee capabilities

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

(defconst ee-example-mode-name "ee-example")

;;; Customizable Variables

(defgroup ee-example nil
  "Accompanying example for demonstration of ee capabilities."
  :prefix "ee-example-"
  :group 'ee)

;;; Data Description and Default Data

(defvar ee-example-data
  '[(meta
     (format-version . "0.0.1")
     (database-version . "0.0.1")
     (data-version . "0.0.1")
     (data-file . "example.ee")
     (view-data-file . "view/example.ee")
     (collector . ee-example-data-collect)
     (fields
      (field (name name))
      (field (name category-1))
      (field (name category-2))
      (field (name category-3))
      (field (name (parent children)))
      (field (name ())))
     (key-fields name)
     (mark-field mark))
    ["ri-101" "c-1" nil "c-4" () ((price . 3.15) (amount . 9))]
    ["ri-102" "c-1/s-1" "c-2/s-2" "c-4" () ((price . 3) (amount . 5))]
    ["ri-103" "c-1" "c-3" "c-4" ((children "ri-104" "ri-105")) ((price . 5) (amount . 7))]
    ["ri-104" nil nil nil ((parent . "ri-103")) ()]
    ["ri-105" nil nil nil ((parent . "ri-104")) ()]])

;;; Data Extraction

(defun ee-example-data-collect (data)
  ;; Copies data as is
  data)

;;; Actions

(defun ee-example-select (&optional arg)
  (interactive)
  (message "%s" (ee-field 'name)))

(defun ee-example-execute (r marks)
  (interactive))

;;; Key Bindings

(defvar ee-example-keymap nil
  "Local keymap for ee-example mode.")

(defun ee-example-keymap-make-default ()
  "Defines default key bindings for `ee-example-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    (define-key map "\C-o" 'ee-example-select)
    (setq ee-example-keymap map)))

(or ee-example-keymap
    (ee-example-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-example (&optional arg)
  "Accompanying example for demonstration of ee capabilities."
  (interactive "P")
  (ee-view-buffer-create
   (format "*%s*" ee-example-mode-name)
   ee-example-mode-name
   ee-example-keymap
   ee-example-data))

(provide 'ee-example)

;;; ee-example.el ends here
