;;; ee-processes.el --- display and manipulate Emacs processes

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

(defconst ee-processes-mode-name "ee-processes")

;;; Customizable Variables

(defgroup ee-processes nil
  "Display and manipulate Emacs processes."
  :prefix "ee-processes-"
  :group 'ee)

;;; Data Description

(defvar ee-processes-data
  '[(meta
     (format-version . "0.0.1")
     (database-version . "0.0.1")
     (view-data-file . "view/processes.ee")
     (collector . ee-processes-data-collect)
     (fields process command id name contact status exit-status tty-name coding-system ())
     (key-fields process))])

;;; Data Extraction

(defun ee-processes-data-collect (data)
  (let* ((field-names (ee-data-field-names data))
         (new-data
          (ee-data-convert-lists-to-vectors
           (mapcar
            (lambda (process)
              (mapcar
               (lambda (field-name)
                 (cond
                  ((eq field-name 'process)
                   process)
                  ((eq field-name 'command)
                   (car (process-command process)))
                  ((eq field-name 'id)
                   (process-id process))
                  ((eq field-name 'name)
                   (process-name process))
                  ((eq field-name 'contact)
                   (process-contact process))
                  ((eq field-name 'status)
                   (process-status process))
                  ((eq field-name 'exit-status)
                   (process-exit-status process))
                  ((eq field-name 'tty-name)
                   (process-tty-name process))
                  ((eq field-name 'coding-system)
                   (process-coding-system process))))
               field-names))
            (process-list)))))
    (aset new-data 0 (aref data 0))
    new-data))

;;; Actions

(defun ee-processes-select (&optional arg other-window)
  (interactive)
  (switch-to-buffer (ee-field 'buffer)))

(defun ee-processes-execute (r marks)
  (mapc (lambda (mark)
          (cond
           ((eq mark ee-mark-del)
            ;; (process-kill-without-query (ee-field 'process r))
            (delete-process (ee-field 'name r)))))
        marks))

;;; Key Bindings

(defvar ee-processes-keymap nil
  "Local keymap for ee-processes mode.")

(defun ee-processes-keymap-make-default ()
  "Defines default key bindings for `ee-processes-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    ;; (define-key map "o" 'ee-processes-switch-to-buffer-other-window)
    ;; (define-key map "\C-o" 'ee-processes-display-buffer)
    (setq ee-processes-keymap map)))

(or ee-processes-keymap
    (ee-processes-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-processes (&optional arg)
  "Display and manipulate Emacs processes."
  (interactive "P")
  (ee-view-buffer-create
   (format "*%s*" ee-processes-mode-name)
   ee-processes-mode-name
   ee-processes-keymap
   ee-processes-data))

(provide 'ee-processes)

;;; ee-processes.el ends here
