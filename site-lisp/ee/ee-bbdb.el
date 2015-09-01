;;; ee-bbdb.el --- summary mode for BBDB

;; Copyright (C) 2002, 2003, 2004, 2010  Juri Linkov <juri@jurta.org>

;; Author: Juri Linkov <juri@jurta.org>
;; Keywords: ee, bbdb

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
  (require 'bbdb-autoloads nil t))

;;; Constants

(defconst ee-bbdb-mode-name "ee-bbdb")

;;; Customizable Variables

(defgroup ee-bbdb nil
  "Summary mode for BBDB."
  :prefix "ee-bbdb-"
  :group 'ee
  :group 'bbdb)

;;; Data Description

(defvar ee-bbdb-data
  '[(meta
     (format-version . "0.0.1")
     (view-data-file . "view/bbdb.ee")
     (collector . ee-bbdb-data-collect)
     (fields bbdb-record ())
     (key-fields bbdb-record))])

;;; Data Extraction

(defun ee-bbdb-data-collect (data)
  (let* ((field-names (ee-data-field-names data))
         (new-data (ee-data-convert-lists-to-vectors
                    (mapcar (lambda (r)
                              (mapcar (lambda (field-name)
                                        (cond
                                         ((eq field-name 'bbdb-record) r)))
                                      field-names))
                            (bbdb-records)))))
    (aset new-data 0 (aref data 0))
    new-data))

;;; Actions

(defun ee-bbdb-create-record (record)
  "Add a new entry to the bbdb database; prompts for all relevant info
using the echo area, inserts the new record in the db, sorted alphabetically,
and offers to save the db file.  DO NOT call this from a program.  Call
bbdb-create-internal instead."
  (interactive (list (bbdb-read-new-record)))
  (bbdb-invoke-hook 'bbdb-create-hook record)
  (bbdb-change-record record t)
  (ee-view-buffer-update t))

(defun ee-bbdb-send-mail (bbdb-record &optional subject)
  "Compose a mail message to the person indicated by the current bbdb record.
The first (most-recently-added) address is used if there are more than one.
\\<bbdb-mode-map>
If \"\\[bbdb-apply-next-command-to-all-records]\\[bbdb-send-mail]\" is \
used instead of simply \"\\[bbdb-send-mail]\", then mail will be sent to \
all of the
folks listed in the *BBDB* buffer instead of just the person at point."
  (interactive (list (ee-field 'bbdb-record)))
  (bbdb-send-mail-1 bbdb-record subject))

(defun ee-bbdb-execute (r marks)
  (mapc (lambda (mark)
          (cond
           ((eq mark ee-mark-del)
            (bbdb-delete-record-internal (ee-field 'bbdb-record r)))))
        marks))

;;; Key Bindings

(defvar ee-bbdb-keymap nil
  "Local keymap for ee-bbdb mode.")

(defun ee-bbdb-keymap-make-default ()
  "Defines default key bindings for `ee-bbdb-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    (define-key map "c" 'ee-bbdb-create-record)
    (define-key map "m" 'ee-bbdb-send-mail)
    (setq ee-bbdb-keymap map)))

(or ee-bbdb-keymap
    (ee-bbdb-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-bbdb (&optional arg)
  "Summary mode for BBDB."
  (interactive "P")
  (require 'bbdb-autoloads)
  (ee-view-buffer-create
   (format "*%s*" ee-bbdb-mode-name)
   ee-bbdb-mode-name
   ee-bbdb-keymap
   ee-bbdb-data))

(provide 'ee-bbdb)

;;; ee-bbdb.el ends here
