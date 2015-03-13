;;; ee-marks.el --- display and go to marked lines in the current Emacs buffer

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

(defconst ee-marks-mode-name "ee-marks")

;;; Customizable Variables

(defgroup ee-marks nil
  "Display and go to marked lines in the current Emacs buffer."
  :prefix "ee-marks-"
  :group 'ee)

;;; Data Description

(defvar ee-marks-data
  '[(meta
     (format-version . "0.0.1")
     (database-version . "0.0.1")
     (view-data-file . "view/marks.ee")
     (collector . ee-marks-data-collect)
     (fields line-number line-string ())
     (key-fields line-number))])

;;; Data Extraction

(defun ee-marks-data-collect (data)
  (let* ((field-names (ee-data-field-names data))
         (new-data
          (ee-data-convert-lists-to-vectors
           (with-current-buffer ee-parent-buffer
             (save-excursion
               (goto-char (point-min))  ; for line-beginning-position
               (mapcar
                (lambda (line-number)
                  (mapcar
                   (lambda (field-name)
                     (cond
                      ((eq field-name 'line-number)
                       line-number)
                      ((eq field-name 'line-string)
                       (buffer-substring
                        (line-beginning-position line-number)
                        (line-end-position line-number)))))
                   field-names))
                (delete-dups
                 (mapcar (lambda (marker)
                           (if (marker-position marker)
                               (1+ (count-lines (point-min)
                                                (marker-position marker)))))
                         (append
                          (list (mark-marker))
                          (delq nil
                                (mapcar (lambda (m)
                                          (and (eq (marker-buffer m)
                                                   (current-buffer))
                                               m))
                                        global-mark-ring))
                          mark-ring)))
                ))))))
    (aset new-data 0 (aref data 0))
    new-data))

;;; Actions

(defun ee-marks-switch-to-buffer (&optional arg other-window)
  (interactive)
  (let ((parent-buffer ee-parent-buffer)
        (line-number (ee-field 'line-number)))
    (when parent-buffer
      (when other-window
        (if (one-window-p)
            (split-window-horizontally))
        (select-window (next-window)))
      (switch-to-buffer parent-buffer)
      (goto-line line-number)
      ;; if only display other window, then return back to view buffer
      (if (eq other-window 'display)
          (select-window (next-window))))))

(defun ee-marks-switch-to-buffer-other-window (&optional arg)
  (interactive)
  (ee-marks-switch-to-buffer arg t))

(defun ee-marks-display-buffer (&optional arg)
  (interactive)
  (ee-marks-switch-to-buffer arg 'display))

(defun ee-marks-execute (r marks)
  ;; TODO: delete mark from mark-ring?
  )

;;; Key Bindings

(defvar ee-marks-keymap nil
  "Local keymap for ee-marks mode.")

(defun ee-marks-keymap-make-default ()
  "Defines default key bindings for `ee-marks-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    (define-key map "o" 'ee-marks-switch-to-buffer-other-window)
    (define-key map "\C-o" 'ee-marks-display-buffer)
    (setq ee-marks-keymap map)))

(or ee-marks-keymap
    (ee-marks-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-marks (&optional arg)
  "Display and go to marked lines in the current Emacs buffer."
  (interactive "P")
  (ee-view-buffer-create
   (format "*%s*/%s" ee-marks-mode-name (buffer-name))
   ee-marks-mode-name
   ee-marks-keymap
   ee-marks-data))

(provide 'ee-marks)

;;; ee-marks.el ends here
