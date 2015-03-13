;;; ee-dired.el --- categorized directory listings

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

(defconst ee-dired-mode-name "ee-dired")

;;; Customizable Variables

(defgroup ee-dired nil
  "Categorized directory listings."
  :prefix "ee-dired-"
  :group 'ee)

;;; Data Description

(defvar ee-dired-data
  '[(meta
     (format-version . "0.0.1")
     (view-data-file . "view/dired.ee")
     (collector . ee-dired-data-collect)
     (fields file-name directory uid gid modtime size modes ())
     (key-fields name))])

;;; Data Extraction

(defun ee-dired-data-collect (data)
  (let ((new-data (ee-data-convert-lists-to-vectors
                   (ee-dired-data-collect-files
                    (ee-data-field-names data)
                    (expand-file-name ".")))))
    (aset new-data 0 (aref data 0))
    new-data))

(defun ee-dired-data-collect-files (field-names dir)
  (if (file-directory-p dir)
      (mapcan
       (lambda (filename)
         (let ((fullname (concat dir filename)))
           (cond
            ((member filename '("." ".."))
             nil)
            ((file-directory-p fullname)
             (ee-dired-data-collect-files
              field-names fullname))
            ((file-exists-p fullname)
             (let ((attr (file-attributes fullname)))
               (list (mapcar (lambda (field-name)
                               (cond
                                ((eq field-name 'file-name) filename)
                                ((eq field-name 'directory) (file-name-directory fullname))
                                ((eq field-name 'uid) (nth 2 attr))
                                ((eq field-name 'gid) (nth 3 attr))
                                ((eq field-name 'modtime) (nth 5 attr))
                                ((eq field-name 'size) (nth 7 attr))
                                ((eq field-name 'modes) (nth 8 attr))))
                             field-names)))))))
       (directory-files (setq dir (file-name-as-directory dir)) nil nil t))))

;;; Actions

(defun ee-dired-find-file (&optional arg)
  (interactive)
  (find-file (expand-file-name (ee-field 'file-name) (ee-field 'directory))))

;;; Key Bindings

(defvar ee-dired-keymap nil
  "Local keymap for ee-dired mode.")

(defun ee-dired-keymap-make-default ()
  "Defines default key bindings for `ee-dired-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    ;; (define-key map "\C-o" 'ee-dired-start-process)
    (setq ee-dired-keymap map)))

(or ee-dired-keymap
    (ee-dired-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-dired (&optional arg)
  "Categorized directory listings."
  (interactive "P")
  (ee-view-buffer-create
   (format "*%s*%s" ee-dired-mode-name (expand-file-name "."))
   ee-dired-mode-name
   ee-dired-keymap
   ee-dired-data))

(provide 'ee-dired)

;;; ee-dired.el ends here
