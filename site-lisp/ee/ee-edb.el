;;; ee-edb.el --- summary mode for EDB

;; Copyright (C) 2002, 2003, 2004, 2010  Juri Linkov <juri@jurta.org>

;; Author: Juri Linkov <juri@jurta.org>
;; Keywords: ee, edb, database, forms

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
  (require 'database nil t)
  (require 'db-summary nil t))

;;; Constants

(defconst ee-edb-mode-name "ee-edb")

;;; Customizable Variables

(defgroup ee-edb nil
  "Summary mode for EDB."
  :prefix "ee-edb-"
  :group 'ee)

;;; Data Description

(defvar ee-edb-data
  '[(meta
     (format-version . "0.0.1")
     (view-data-file . "view/edb.ee")
     (collector . ee-edb-data-collect)
     (fields edb-record ())
     ;; (key-fields edb-record)
     )])

;;; Data Extraction

(defun ee-edb-data-collect (data)
  (setq dbs-no-of-records -1)
  (setq dbc-database (with-current-buffer ee-parent-buffer dbc-database))
  (let* ((field-names (ee-data-field-names data))
         (new-data (ee-data-convert-lists-to-vectors
                    (with-current-buffer ee-parent-buffer
                      (let ((data-display-buffer (current-buffer))
                            res)
                        (if (not dbf-summary-function)
                            (dbf-set-summary-format dbf-summary-format))
                        (if (not (dbf-summary-buffer))
                            (setq dbf-summary-buffer
                                  (db-create-summary-buffer data-display-buffer)))
                        (setq dbs-data-display-buffer data-display-buffer)
                        (maplinks-macro
                         (let ((r maplinks-link)
                               (summary-function dbf-summary-function)
                               (recompute-all-p dbf-summary-recompute-all-p))
                           (if (or recompute-all-p (not (link-summary maplinks-link)))
                               (progn
                                 (db-debug-message "Computing link summary for link %d." maplinks-index)
                                 (link-set-summary maplinks-link
                                                   (funcall summary-function (link-record maplinks-link)))))
                           (setq res (cons (mapcar (lambda (field-name)
                                                     (cond
                                                      ((eq field-name 'edb-record) maplinks-link)))
                                                   field-names) res)))
                         dbc-database nil "Computing summary...%d")
                        (nreverse res))))))
    (aset new-data 0 (aref data 0))
    new-data))

;;; Actions

(defun ee-edb-switch-to-buffer (&optional arg)
  (interactive "P")
  (let ((ri (ee-view-record-index-get (point))))
    (when (and ri ee-parent-buffer)
      (switch-to-buffer ee-parent-buffer)
      (db-jump-to-record ri))))

;;; Key Bindings

(defvar ee-edb-keymap nil
  "Local keymap for ee-edb mode.")

(defun ee-edb-keymap-make-default ()
  "Defines default key bindings for `ee-edb-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (and (boundp 'database-view-mode-map)
       (let ((map (copy-keymap ee-mode-map)))
         ;; (define-key map "c" 'ee-edb-create-record)
         (define-key database-view-mode-map "H" 'ee-edb)
         (setq ee-edb-keymap map))))

(or ee-edb-keymap
    (ee-edb-keymap-make-default))

;;;###autoload
(defun ee-edb (&optional arg)
  "Summary mode for EDB."
  (interactive "P")
  (require 'database)
  (require 'db-summary)
  (ee-view-buffer-create
   (format "*%s*/%s" ee-edb-mode-name (buffer-name))
   ee-edb-mode-name
   ee-edb-keymap
   ee-edb-data))

(provide 'ee-edb)

;;; ee-edb.el ends here
