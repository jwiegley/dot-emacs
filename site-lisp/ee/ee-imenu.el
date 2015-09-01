;;; ee-imenu.el --- categorized mode-specific buffer indexes

;; Copyright (C) 2002, 2003, 2004, 2010  Juri Linkov <juri@jurta.org>

;; Author: Juri Linkov <juri@jurta.org>
;; Keywords: ee, tools, convenience

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

(eval-when-compile
  (require 'imenu nil t))

;;; Constants

(defconst ee-imenu-mode-name "ee-imenu")

;;; Customizable Variables

(defgroup ee-imenu nil
  "Categorized mode-specific buffer indexes."
  :prefix "ee-imenu-"
  :group 'ee)

;;; Data Description

(defvar ee-imenu-data
  '[(meta
     (format-version . "0.0.1")
     (view-data-file . "view/imenu.ee")
     (collector . ee-imenu-data-collect)
     (fields name position-marker category ())
     (key-fields name category))])

;;; Data Extraction

(defun ee-imenu-data-collect (data)
  (let ((old-data (if ee-data
                      (mapcar (lambda (r)
                                (ee-field 'name r))
                              (ee-data-records-find ee-data '(read . t)))))
        (new-data (ee-data-convert-lists-to-vectors
                   (ee-imenu-data-collect-items
                    nil   ; name of the root category (nil by default)
                    (with-current-buffer ee-parent-buffer
                      (save-excursion
                        (save-restriction
                          (widen)
                          (funcall imenu-create-index-function))))
                    (ee-data-field-names data)))))
    (aset new-data 0 (aref data 0))
    (if old-data
        (ee-data-records-do
         new-data
         (lambda (r ri)
           (if (member (ee-field 'name r) old-data)
               (ee-field-set 'read t r (ee-data-meta-setters-get-set new-data))))))
    new-data))

(defun ee-imenu-data-collect-items (name imenu-items field-names)
  "Convert imenu internal data structure into relational database."
  (let (res)
    (while imenu-items
      (let ((item (car imenu-items)))
        (setq res (nconc ;append?
                   res
                   (if (consp (cdr item))
                       (ee-imenu-data-collect-items
                        (if (stringp name)
                            (concat name "/" (car item))
                          (car item))
                        (cdr item)
                        field-names)
                     (list
                      (mapcar (lambda (field-name)
                                (cond
                                 ((eq field-name 'name) (car item))
                                 ((eq field-name 'position-marker) (cdr item))
                                 ((eq field-name 'category) name)))
                              field-names))))
              imenu-items (cdr imenu-items))))
    res))

;;; Actions

(defun ee-imenu-switch-to-buffer (&optional arg other-window)
  (interactive)
  (let ((marker (ee-field 'position-marker))
        (parent-buffer ee-parent-buffer))
    ;; mark as read and update view
    (ee-field-set 'read t)
    (ee-view-update '(read)) ;; (ee-view-record-update)
    (when (and marker parent-buffer)
      (when other-window
        (if (one-window-p)
            (split-window-horizontally))
        (select-window (next-window)))
      (switch-to-buffer parent-buffer)
      (goto-char marker)
      (set-window-start nil marker)
      ;; if only display other window, then return back to view buffer
      (if (eq other-window 'display)
          (select-window (next-window))))))

(defun ee-imenu-switch-to-buffer-other-window (&optional arg)
  (interactive)
  (ee-imenu-switch-to-buffer arg t))

(defun ee-imenu-display-buffer (&optional arg)
  (interactive)
  (ee-imenu-switch-to-buffer arg 'display))

(defun ee-imenu-execute (r marks)
  ;; TODO: delete referenced region from parent buffer
  )

;;; Key Bindings

(defvar ee-imenu-keymap nil
  "Local keymap for ee-imenu-mode buffers.")

(defun ee-imenu-keymap-make-default ()
  "Defines default key bindings for `ee-imenu-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    (define-key map "o" 'ee-imenu-switch-to-buffer-other-window)
    (define-key map "\C-o" 'ee-imenu-display-buffer)
    (setq ee-imenu-keymap map)))

(or ee-imenu-keymap
    (ee-imenu-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-imenu (&optional arg)
  "Categorized mode-specific buffer indexes."
  (interactive "P")
  (require 'imenu)
  (ee-view-buffer-create
   (format "*%s*/%s" ee-imenu-mode-name (buffer-name))
   ee-imenu-mode-name
   ee-imenu-keymap
   ee-imenu-data))

(provide 'ee-imenu)

;;; ee-imenu.el ends here
