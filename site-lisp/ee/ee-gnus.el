;;; ee-gnus.el --- summary and topic mode for Gnus

;; Copyright (C) 2002, 2003, 2004, 2010  Juri Linkov <juri@jurta.org>

;; Author: Juri Linkov <juri@jurta.org>
;; Keywords: ee, gnus

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
  (require 'gnus))

;;; Constants

(defconst ee-gnus-mode-name "ee-gnus")

;;; Customizable Variables

(defgroup ee-gnus nil
  "Summary and topic mode for Gnus."
  :prefix "ee-gnus-"
  :group 'ee
  :group 'gnus)

;;; Data Description

(defvar ee-gnus-data
  '[(meta
     (format-version . "0.0.1")
     (view-data-file . "view/gnus.ee")
     (collector . ee-gnus-data-collect)
     (fields name category unread ())
     (key-fields name))])

;;; Data Extraction

(defun ee-gnus-data-collect (data)
  (let* ((field-names (ee-data-field-names data))
         (categories-alist (ee-gnus-data-categories gnus-topic-topology ""))
         (new-data
          (ee-data-convert-lists-to-vectors
           (mapcan (lambda (topic)
                     (let ((category (or (cdr (assoc (car topic) categories-alist))
                                         (car topic))))
                       (mapcar (lambda (group)
                                 (mapcar (lambda (field-name)
                                           (cond
                                            ((eq field-name 'name) group)
                                            ((eq field-name 'category) category)
                                            ;; TODO: where to get unread?
                                            ((eq field-name 'unread) "*")))
                                         field-names))
                               (cdr topic))))
                   gnus-topic-alist))))
    (aset new-data 0 (aref data 0))
    new-data))

(defun ee-gnus-data-categories (topology category)
  (let ((topic (car topology))
        (topics (cdr topology)))
    (append
     (list (cons (car topic) (concat category (car topic))))
     (mapcan (lambda (elt)
               (ee-gnus-data-categories elt (concat category (car topic) "/")))
             topics))))

;;; Actions

(defun ee-gnus-execute (r marks)
  (mapc (lambda (mark)
          (cond
           ((eq mark ee-mark-del)
            ;; (gnus-delete-group-internal (ee-field 'name r))
            )))
        marks))

;;; Key Bindings

(defvar ee-gnus-keymap nil
  "Local keymap for ee-gnus mode.")

(defun ee-gnus-keymap-make-default ()
  "Defines default key bindings for `ee-gnus-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    (define-key map "c" 'ee-gnus-create-record)
    (define-key map "m" 'ee-gnus-send-mail)
    (setq ee-gnus-keymap map)))

(or ee-gnus-keymap
    (ee-gnus-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-gnus (&optional arg)
  "Summary and topic mode for Gnus."
  (interactive "P")
  (require 'gnus)
  (ee-view-buffer-create
   (format "*%s*" ee-gnus-mode-name)
   ee-gnus-mode-name
   ee-gnus-keymap
   ee-gnus-data))

(provide 'ee-gnus)

;;; ee-gnus.el ends here
