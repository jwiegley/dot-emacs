;;; ee-tags.el --- etags facility

;; Copyright (C) 2002, 2003, 2004, 2010  Juri Linkov <juri@jurta.org>

;; Author: Juri Linkov <juri@jurta.org>
;; Keywords: ee, tags

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
  (require 'etags))

;;; Constants

(defconst ee-tags-mode-name "ee-tags")

;;; Customizable Variables

(defgroup ee-tags nil
  "Etags facility."
  :prefix "ee-tags-"
  :group 'ee)

;;; Data Description

(defvar ee-tags-data
  '[(meta
     (format-version . "0.0.1")
     (database-version . "0.0.1")
     (view-data-file . "view/tags.ee")
     (collector . ee-tags-data-collect)
     (fields file tag text line startpos ())
     (key-fields file startpos))])

;;; Data Extraction

(defun ee-tags-data-collect (data)
  (let* ((field-names (ee-data-field-names data))
         (old-data (if ee-data
                       (mapcar (lambda (r)
                                 (ee-field 'tag r))
                               (ee-data-records-find ee-data '(read . t)))))
         (new-data
          (ee-data-convert-lists-to-vectors
           (mapcar
            (lambda (tag)
              (mapcar
               (lambda (field-name)
                 (cond
                  ((eq field-name 'file)     (nth    0 tag))
                  ((eq field-name 'tag)      (nth    1 tag))
                  ((eq field-name 'text)     (nth    2 tag))
                  ((eq field-name 'line)     (nth    3 tag))
                  ((eq field-name 'startpos) (nthcdr 4 tag)))) field-names))
            (ee-tags-data-collect-tags)))))
    (aset new-data 0 (aref data 0))
    (if old-data
        (ee-data-records-do
         new-data
         (lambda (r ri)
           (if (member (ee-field 'tag r) old-data)
               (ee-field-set 'read t r (ee-data-meta-setters-get-set new-data))))))
    new-data))

(defun ee-tags-data-collect-tags ()
  (let ((res))
    (save-excursion
      (visit-tags-table-buffer)
      (mapc
       (lambda (file)
         ;; adapted from `etags-list-tags' that needs rewriting
         (goto-char 1)
         (when (search-forward (concat "\f\n" file ",") nil t)
           (forward-line 1)
           (while (not (or (eobp) (looking-at "\f")))
             (let ((tag (buffer-substring (point)
                                          (progn (skip-chars-forward "^\177")
                                                 (point)))))
               (when (looking-at "[^\n]+\001")
                 ;; There is an explicit tag name; use that.
                 (setq tag (buffer-substring (1+ (point)) ; skip \177
                                             (progn (skip-chars-forward "^\001")
                                                    (point)))))
               (beginning-of-line)            ; for `etags-snarf-tag'
               (setq res (cons (cons file (cons tag (etags-snarf-tag))) res))))
           t))
       (etags-tags-table-files)))
    res))

;;; Actions

;; TODO: take hair from `find-tag-other-window'
(defun ee-tags-select (&optional arg other-window)
  (interactive)
  (ee-field-set 'read t)
  (ee-view-update '(read)) ;; (ee-view-record-update)
  ;; adapted from `find-tag-in-order' that needs rewriting
  (let ((tag-info (cons (ee-field 'text) (cons (ee-field 'line)
                                               (ee-field 'startpos)))))
    (find-file (expand-file-name (ee-field 'file)
                                 (save-excursion
                                   (visit-tags-table-buffer)
                                   default-directory)))
    (etags-goto-tag-location tag-info)))

;;; Key Bindings

(defvar ee-tags-keymap nil
  "Local keymap for ee-tags mode.")

(defun ee-tags-keymap-make-default ()
  "Defines default key bindings for `ee-tags-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    ;; (define-key map "o" 'ee-tags-switch-to-buffer-other-window)
    ;; (define-key map "\C-o" 'ee-tags-display-buffer)
    (setq ee-tags-keymap map)))

(or ee-tags-keymap
    (ee-tags-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-tags (&optional arg)
  "Etags facility."
  (interactive "P")
  (require 'etags)
  (ee-view-buffer-create
   (format "*%s*" ee-tags-mode-name)
   ee-tags-mode-name
   ee-tags-keymap
   ee-tags-data
   ;; TODO: save to data file?
   ))

(provide 'ee-tags)

;;; ee-tags.el ends here
