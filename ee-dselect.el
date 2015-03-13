;;; ee-dselect.el --- Debian package handling frontend

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

(defconst ee-dselect-mode-name "ee-dselect")

;;; Customizable Variables

(defgroup ee-dselect nil
  "Debian package handling frontend."
  :group 'ee)

(defcustom ee-dselect-admindir "/var/lib/dpkg"
  "Directory where the dpkg `status', `available' or similar files
are located.  This defaults to /var/lib/dpkg and normally there
shouldn't be any need to change it."
  :type 'string
  :group 'ee-dselect)

(defcustom ee-dselect-fields '("Package" "Priority" "Section" "Installed-Size" "Maintainer" "Architecture" "Source" "Version" "Replaces" "Depends" "Filename" "Size")
  ;; TODO: fetch only fields mentioned in view description?
  ;;       bad, because needs every time to parse 'available'
  ;; this variable defines all fields in ee-dselect-data,
  ;; but data-descr's fields that only used in current view
  "File fields."
  :type '(repeat string)
  :group 'ee-dselect)

(defvar ee-dselect-file-name-available "available"
  "File name of `available' file.")

(defvar ee-dselect-file-name-status "status"
  "File name of `status' file.")

(defvar ee-dselect-data-cache nil
  "Cahce for data fetched from file.")

;;; Data Description

(defvar ee-dselect-data
  '[(meta
     (format-version . "0.0.1")
     (view-data-file . "view/dselect.ee")
     (data-file . "dselect.ee")
     (collector . ee-dselect-data-collect)
     (fields package priority section installed-size maintainer architecture source version replaces depends filename size description ())
     (key-fields package))])

;;; Data Extraction

(defun ee-dselect-data-collect (data)
  (let ((new-data (or ee-dselect-data-cache
                      ;; TODO: move to ee.el
                      (setq ee-dselect-data-cache (ee-dselect-read-data)))))
    (aset new-data 0 (aref data 0))
    new-data))

(defun ee-dselect-read-data ()
  (let ((fields-len (+ 2 (length ee-dselect-fields)))
        (fields-re (concat "^" (regexp-opt ee-dselect-fields t) ": "))
        ;; (setq fields-re (concat "^\\(" (mapconcat 'regexp-quote ee-dselect-fields "\\|") "\\): \\(.*\\)")) ; times - 14 sec vs. 16 sec
        ;; (setq fields-re (concat "^\\(" (mapconcat 'regexp-quote ee-dselect-fields "\\|") "\\): ")) ; times - 14 sec vs. 16 sec
        )
    (apply
     'vector
     (let (l v b d)
       (with-current-buffer (ee-dselect-get-buffer-available)
         (widen)
         (goto-char (point-min))
         (while (not (eobp))
           (if (looking-at "^Package:")
               (setq v (make-vector fields-len nil)
                     b (point)))
           (if (looking-at fields-re)
               (aset v (- fields-len 2 (length (member
                                              (buffer-substring (point) (- (match-end 0) 2))
                                              ;; (match-string 1) ; don't work with (regexp-opt)
                                              ee-dselect-fields)))
                     (buffer-substring (match-end 0) (progn (end-of-line) (point)))
                     ;; (match-string 2) ; don't work with (regexp-opt)
                     ))
           (if (not (looking-at "^Description:"))
               (forward-line 1)
             (setq d (point))
             (search-forward "\n\n")
             (aset v (- fields-len 2) (list b d (point)))
             (aset v 3 (string-to-int (aref v 3))) ; bad hack
             (aset v 11 (string-to-int (aref v 11))) ; bad hack
             (push v l))))
       (nreverse l)))))

;; TODO: ee-dselect-search-string-in-description and
;;       ee-dselect-get-description-as-string are slow,
;;       so make function to search string directly in `available' buffer
;;       and collect package names where string is found

(defun ee-dselect-search-string-in-description (r string)
  (save-excursion
    (with-current-buffer (ee-dselect-get-buffer-available)
      (widen)
      (goto-char (cadr (aref r (length ee-dselect-fields))))
      (search-forward string (caddr (aref r (length ee-dselect-fields))) t))))

(defun ee-dselect-get-description-as-string (r)
  (save-excursion
    (with-current-buffer (ee-dselect-get-buffer-available)
      (widen)
      (buffer-substring-no-properties
       ;; 12 is the length of the string "Description:"
       (+ 12 (cadr (aref r (length ee-dselect-fields))))
       (caddr (aref r (length ee-dselect-fields)))
       ))))

(defun ee-dselect-get-buffer-available ()
  (find-file-noselect (concat ee-dselect-admindir "/" ee-dselect-file-name-available)))

;;; Actions

(defun ee-dselect-display-info-with-narrow (&optional arg)
  (interactive)
  (let* ((d (ee-field 'description))
         ;; 12 is the length of the string "Description:"
         (b (and d (+ (cadr d) 12))))
    (when (and d b)
      (with-current-buffer (ee-dselect-get-buffer-available)
        (narrow-to-region b (caddr d))
        (goto-char b))
      (set-window-start (display-buffer (ee-dselect-get-buffer-available)) b))))

(defun ee-dselect-display-description-with-narrow (&optional arg)
  (interactive)
  (let* ((d (ee-field 'description))
         ;; 12 is the length of the string "Description:"
         (b (and d (+ (car d) 12))))
    (when (and d b)
      (with-current-buffer (ee-dselect-get-buffer-available)
        (narrow-to-region b (caddr d))
        (goto-char b))
      (set-window-start (display-buffer (ee-dselect-get-buffer-available)) b))))

;;; Key Bindings

(defvar ee-dselect-keymap nil
  "Local keymap for ee-dselect mode.")

(defun ee-dselect-keymap-make-default ()
  "Defines default key bindings for `ee-dselect-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    (define-key map "i" 'ee-dselect-display-description-with-narrow)
    (define-key map "o" 'ee-dselect-display-info-with-narrow)
    (define-key map "\C-o" 'ee-dselect-display-info-with-narrow)
    (setq ee-dselect-keymap map)))

(or ee-dselect-keymap
    (ee-dselect-keymap-make-default))

;;;###autoload
(defun ee-dselect (&optional arg)
  "Debian package handling frontend."
  (interactive "P")
  (ee-view-buffer-create
   (format "*%s*" ee-dselect-mode-name)
   ee-dselect-mode-name
   ee-dselect-keymap
   ee-dselect-data
   nil
   nil
   nil
   nil ;; TEST: try add here data file name
   t ;; auto-save
   ))

(provide 'ee-dselect)

;;; ee-dselect.el ends here
