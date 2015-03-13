;;; ee-windows.el --- display and switch Emacs window configurations

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

;; The command `ee-windows-add' adds the current window configuration
;; to the global list of window configurations.
;; Then the command `ee-windows' can be called
;; to display and switch added window configurations.

;; See the file README and documentation for more information.

;;; Code:

(require 'ee)

;;; Constants

(defconst ee-windows-mode-name "ee-windows")

;;; Customizable Variables

(defgroup ee-windows nil
  "Display and switch Emacs window configurations."
  :prefix "ee-windows-"
  :group 'ee)

;;; Data Description

(defvar ee-windows-data
  '[(meta
     (format-version . "0.0.1")
     (database-version . "0.0.1")
     (view-data-file . "view/windows.ee")
     (collector . ee-windows-data-collect)
     (fields window-configuration buffer-names buffer-list buried-buffer-list ())
     (key-fields window-configuration))])

;;; Data Extraction

(defun ee-windows-data-collect (data)
  ;; Returns global data value as is
  ee-windows-data)

;;; Actions

(defun ee-windows-select (&optional arg)
  (interactive)
  (let ((wc (ee-field 'window-configuration))
        (bl (delq nil (mapcar (lambda (b) (and (buffer-live-p b) b))
                              (ee-field 'buffer-list))))
        (bbl (delq nil (mapcar (lambda (b) (and (buffer-live-p b) b))
                               (ee-field 'buried-buffer-list)))))
    (modify-frame-parameters (selected-frame) (list (cons 'buffer-list bl)))
    (modify-frame-parameters (selected-frame) (list (cons 'buried-buffer-list bbl)))
    (set-window-configuration wc)))

(defun ee-windows-select-and-delete-current (&optional arg)
  (interactive)
  (let ((wc (ee-field 'window-configuration))
        (bl (delq nil (mapcar (lambda (b) (and (buffer-live-p b) b))
                              (ee-field 'buffer-list))))
        (bbl (delq nil (mapcar (lambda (b) (and (buffer-live-p b) b))
                               (ee-field 'buried-buffer-list))))
        (ri (ee-view-record-index-get (point))))
    (ee-data-record-delete ri t)
    (setq ee-windows-data ee-data)
    (kill-buffer (current-buffer))
    (modify-frame-parameters (selected-frame) (list (cons 'buffer-list bl)))
    (modify-frame-parameters (selected-frame) (list (cons 'buried-buffer-list bbl)))
    (set-window-configuration wc)))

(defun ee-windows-execute (r marks)
  (interactive)
  ;; TODO: make general function in ee.el
  ;; to delete empty rows (rows with nil values)
  )

;;;###autoload
(defun ee-windows-and-add-current (&optional arg)
  (interactive)
  (ee-windows-add)
  (ee-windows arg)
  (modify-frame-parameters (selected-frame) (list (cons 'buffer-list nil)))
  (modify-frame-parameters (selected-frame) (list (cons 'buried-buffer-list nil))))

;;; Key Bindings

(defvar ee-windows-keymap nil
  "Local keymap for ee-windows mode.")

(defun ee-windows-keymap-make-default ()
  "Defines default key bindings for `ee-windows-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    ;; (define-key map "\C-o" 'ee-windows-select)
    (setq ee-windows-keymap map)))

(or ee-windows-keymap
    (ee-windows-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-windows-add ()
  "Add current Emacs window configuration."
  (interactive)
  (ee-data-record-add
   (vector
    (apply 'vector (mapcar
                    (lambda (field-name)
                      (cond
                       ((eq field-name 'window-configuration)
                        (current-window-configuration))
                       ((eq field-name 'buffer-names)
                        (mapconcat
                         (lambda (w) (buffer-name (window-buffer w)))
                         (window-list)
                         ", "))
                       ((eq field-name 'buffer-list)
                        (delq nil (mapcar
                                   (lambda (b) (and (buffer-live-p b) b))
                                   (frame-parameter (selected-frame)
                                                    'buffer-list))))
                       ((eq field-name 'buried-buffer-list)
                        (delq nil (mapcar
                                   (lambda (b) (and (buffer-live-p b) b))
                                   (frame-parameter (selected-frame)
                                                    'buried-buffer-list))))))
                    (ee-data-meta-field-get ee-windows-data 'fields))))
   'ee-windows-data)
  ;;   (message "Current window configuration added")
  )

;;;###autoload
(defun ee-windows (&optional arg)
  "Display and switch Emacs window configurations."
  (interactive "P")
  (ee-view-buffer-create
   (format "*%s*" ee-windows-mode-name)
   ee-windows-mode-name
   ee-windows-keymap
   ee-windows-data)
  (if (< (ee-data-size ee-windows-data) 1)
      (message
       (substitute-command-keys
        "No window configurations yet. You can add a new by \\[ee-windows-add]")))
  ;; (run-hooks 'ee-windows-hook)
  )

(provide 'ee-windows)

;;; ee-windows.el ends here
