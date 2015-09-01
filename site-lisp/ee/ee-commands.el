;;; ee-commands.el --- categorized menu of Emacs commands

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

(defconst ee-commands-mode-name "ee-commands")

;;; Customizable Variables

(defgroup ee-commands nil
  "Categorized menu of Emacs commands."
  :prefix "ee-commands-"
  :group 'ee)

(defcustom ee-commands-record-flag nil
  "Put the called command in the command-history."
  :type 'boolean
  :group 'ee-commands)

;;; Data Description

(defvar ee-commands-data
  '[(meta
     (format-version . "0.0.1")
     (view-data-file . "view/commands.ee")
     (collector . ee-commands-data-collect)
     (fields name command documentation ())
     (key-fields command))])

;;; Data Extraction

(defun ee-commands-data-collect (data)
  (let* ((field-names (ee-data-field-names data))
         (new-data
          (ee-data-convert-lists-to-vectors
           (let (res)
             (mapatoms (lambda (s)
                         (if (and (functionp s) (commandp s))
                             (push s res))))
             (mapcar (lambda (s)
                       (mapcar (lambda (field-name)
                                 (cond
                                  ((eq field-name 'name) (symbol-name s))
                                  ((eq field-name 'command) s)
                                  ((eq field-name 'documentation)
                                   (let ((doc (documentation s)))
                                     (if doc
                                         (substring doc 0 (string-match "\n" doc)))))))
                               field-names))
                     (sort res (lambda (s1 s2)
                                 (string< (symbol-name s1)
                                          (symbol-name s2)))))))))
    (aset new-data 0 (aref data 0))
    new-data))

;;; Actions

(defun ee-commands-call-interactively (&optional arg)
  (interactive)
  (let ((command (ee-field 'command))
        (parent-buffer ee-parent-buffer))
    (when (and command parent-buffer)
      (switch-to-buffer parent-buffer)
      (call-interactively command ee-commands-record-flag))))

;;; Key Bindings

(defvar ee-commands-keymap nil
  "Local keymap for ee-commands mode.")

(defun ee-commands-keymap-make-default ()
  "Defines default key bindings for `ee-commands-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    ;; (define-key map "\C-o" 'ee-commands-call-interactively)
    (setq ee-commands-keymap map)))

(or ee-commands-keymap
    (ee-commands-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-commands (&optional arg)
  "Categorized menu of Emacs commands."
  (interactive "P")
  (ee-view-buffer-create
   (format "*%s*" ee-commands-mode-name)
   ee-commands-mode-name
   ee-commands-keymap
   ee-commands-data))

(provide 'ee-commands)

;;; ee-commands.el ends here
