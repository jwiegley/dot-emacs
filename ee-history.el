;;; ee-history.el --- display lists from Emacs history variables

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

(eval-when-compile
  (require 'cl))

;;; Constants

(defconst ee-history-mode-name "ee-history")

;;; Customizable Variables

(defgroup ee-history nil
  "Display lists from Emacs history variables."
  :prefix "ee-history-"
  :group 'ee)

(defcustom ee-history-record-flag nil
  "Put the called command in the command-history."
  :type 'boolean
  :group 'ee-history)

(defcustom ee-history-delete-duplicates t
  "Remove all duplicate elements from history."
  :type 'boolean
  :group 'ee-history)

;;; Buffer-Local Variables

(defvar ee-history-type nil
  "Type of history.")
(make-variable-buffer-local 'ee-history-type)

;;; Data Description

(defvar ee-history-data
  '[(meta
     (format-version . "0.0.1")
     (view-data-file . "view/history.ee")
     (collector . ee-history-data-collect)
     (fields name ())
     (key-fields name))])

;;; Data Extraction

(defun ee-history-data-collect (data)
  (let* ((field-names (ee-data-field-names data))
         (new-data
          (ee-data-convert-lists-to-vectors
           (let ((res
                  (mapcar (lambda (s)
                            (mapcar (lambda (field-name)
                                      (cond
                                       ((eq field-name 'name) s)))
                                    field-names))
                          (reverse
                           (cond
                            ;; TODO: use ee-history-type somehow
                            ((equal (buffer-name) (format "*%s/command*" ee-history-mode-name))
                             command-history)
                            ((equal (buffer-name) (format "*%s/extended-command*" ee-history-mode-name))
                             extended-command-history)
                            ((equal (buffer-name) (format "*%s/shell-command*" ee-history-mode-name))
                             shell-command-history))))))
             (if ee-history-delete-duplicates
                 (setq res (delete-dups res)))
             res))))
    (aset new-data 0 (aref data 0))
    new-data))

;;; Actions

(defun ee-history-select (&optional arg)
  (let ((name (ee-field 'name))
        (parent-buffer ee-parent-buffer)
        (type ee-history-type))
    (when (and name parent-buffer)
      ;; TODO: make and use new function ee-switch-to-buffer,
      ;; which switches iff parent-buffer still exists
      (switch-to-buffer parent-buffer)
      (cond
       ((eq type 'command)
        (setq command-history (cons name command-history))
        (eval name))
       ((eq type 'extended-command)
        (setq extended-command-history (cons name extended-command-history))
        (call-interactively (intern name) ee-history-record-flag))
       ((eq type 'shell-command)
        (setq shell-command-history (cons name shell-command-history))
        (shell-command name))))))

;; TODO: if ee-history-delete-duplicates is nil, then mark all duplicates
(defun ee-history-execute (r marks)
  (mapc (lambda (mark)
          (cond
           ((eq mark ee-mark-del)
            (cond
             ((eq ee-history-type 'command)
              (setq command-history (delete (ee-field 'name r) command-history)))
             ((eq ee-history-type 'extended-command)
              (setq extended-command-history (delete (ee-field 'name r) extended-command-history)))
             ((eq ee-history-type 'shell-command)
              (setq shell-command-history (delete (ee-field 'name r) shell-command-history)))))))
        marks))

;;; Key Bindings

(defvar ee-history-keymap nil
  "Local keymap for ee-history mode.")

(defun ee-history-keymap-make-default ()
  "Defines default key bindings for `ee-history-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    ;; (define-key map "\C-o" 'ee-history-select)
    (setq ee-history-keymap map)))

(or ee-history-keymap
    (ee-history-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-history-command (&optional arg)
  "Display list from Emacs variable `command-history'."
  (interactive "P")
  (ee-view-buffer-create
   (format "*%s/command*" ee-history-mode-name)
   ee-history-mode-name
   ee-history-keymap
   ee-history-data)
  (setq ee-history-type 'command))

;;;###autoload
(defun ee-history-extended-command (&optional arg)
  "Display list from Emacs variable `extended-command-history'."
  (interactive "P")
  (ee-view-buffer-create
   (format "*%s/extended-command*" ee-history-mode-name)
   ee-history-mode-name
   ee-history-keymap
   ee-history-data)
  (setq ee-history-type 'extended-command))

;;;###autoload
(defun ee-history-shell-command (&optional arg)
  "Display list from Emacs variable `shell-command-history'."
  (interactive "P")
  (ee-view-buffer-create
   (format "*%s/shell-command*" ee-history-mode-name)
   ee-history-mode-name
   ee-history-keymap
   ee-history-data)
  (setq ee-history-type 'shell-command))

(provide 'ee-history)

;;; ee-history.el ends here
