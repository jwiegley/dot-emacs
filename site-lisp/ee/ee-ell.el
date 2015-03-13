;;; ee-ell.el --- browse the categorized Emacs Lisp List

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

(defconst ee-ell-mode-name "ee-ell")

;;; Customizable Variables

(defgroup ee-ell nil
  "Browse the categorized Emacs Lisp List."
  :prefix "ee-ell-"
  :group 'ee)

(defcustom ee-ell-url "http://www.damtp.cam.ac.uk/user/sje30/emacs/ell"
  ;; "http://anc.ed.ac.uk/~stephen/emacs/ell" - Moved Permanently
  "URL of the Emacs Lisp List."
  :type 'string
  :group 'ee-ell)

(defcustom ee-ell-install-dir "~/.emacs.d/ell/"
  "Path to install downloaded Emacs packages."
  :type 'string
  :group 'ee-ell)

;;; Global Variables

(defvar ee-ell-mark-install 'i
  "Symbol used to mark records for installing.")

(defvar ee-ell-mark-uninstall 'u
  "Symbol used to mark records for uninstalling.")

;;; Data Description and Default Data

(defvar ee-ell-data
  '[(meta
     (format-version . "0.0.1")
     (database-version . "0.0.1")
     (data-version . "0.0.1")
     (data-file . "ell.ee")
     (view-data-file . "view/ell.ee")
     (collector . ee-ell-data-collect)
     (fields name desc date site auth note ())
     (key-fields name)
     (mark-field mark))])

;;; Data Extraction

(defun ee-ell-data-collect (data)
  (let* ((field-names (ee-data-field-names data))
         (new-data
          (ee-data-convert-lists-to-vectors
           (with-temp-buffer
             (let (name desc date site auth note res)
               (message "Retrieving ell...")
               (url-insert-file-contents ee-ell-url)
               (message "Retrieving ell...done")
               (goto-char (point-min))
               (while (not (looking-at "^Authors:\\|### Local Variables"))
                 (cond
                  ((looking-at "^;;; +\\([^ ]+\\) +--- +\\(.*\\)")
                   (setq name (match-string 1)
                         desc (match-string 2)))
                  ((looking-at "^D: \\(.*\\)")
                   (setq date (match-string 1)))
                  ((looking-at "^S: \\(.*\\)")
                   (setq site (cons (match-string 1) site)))
                  ((looking-at "^A: \\(.*\\)")
                   (setq auth (match-string 1)))
                  ((looking-at "^N: \\(.*\\)")
                   (setq note (match-string 1)))
                  ((looking-at "^$")
                   (if name
                       (setq res
                             (cons
                              (mapcar
                               (lambda (field-name)
                                 (cond
                                  ((eq field-name 'name) name)
                                  ((eq field-name 'desc) desc)
                                  ((eq field-name 'date) date)
                                  ((eq field-name 'site) (reverse site))
                                  ((eq field-name 'auth) auth)
                                  ((eq field-name 'note) note)))
                               field-names)
                              res)))
                   (setq name nil desc nil date nil
                         site nil auth nil note nil)))
                 (forward-line 1))
               (nreverse res))))))
    (aset new-data 0 (aref data 0))
    new-data))

;;; Actions

(defun ee-ell-select (&optional arg)
  (interactive)
  (message "%s" (ee-view-record-get)))

(defun ee-ell-mark-install (&optional arg)
  "Mark package on this line to be installed by \\<ee-mode-map>\\[ee-view-records-execute] command.
Prefix arg is how many records to install.
Negative arg means install backwards."
  (interactive "p")
  (ee-view-mark-lines ee-data-mark-field-name ee-ell-mark-install arg))

(defun ee-ell-mark-uninstall (&optional arg)
  "Mark package on this line to be uninstalled by \\<ee-mode-map>\\[ee-view-records-execute] command.
Prefix arg is how many records to uninstall.
Negative arg means uninstall backwards."
  (interactive "p")
  (ee-view-mark-lines ee-data-mark-field-name ee-ell-mark-uninstall arg))

(defun ee-ell-execute (r marks)
  (mapc (lambda (mark)
          (cond
           ((eq mark ee-ell-mark-install)
            (ee-ell-install r))
           ((eq mark ee-ell-mark-uninstall)
            (ee-ell-uninstall r))))
        marks))

(defun ee-ell-install (r)
  (interactive)
  (let* ((url (car (ee-field 'site r)))
         (local-file (concat ee-ell-install-dir (file-name-nondirectory url))))
    (when (string-match "\\.el" url)
      (with-temp-buffer
        (let* ((host (and (string-match "^http://\\([^/]+\\)" url)
                          (match-string-no-properties 1 url)))
               (path (and (string-match "^http://[^/]+/\\(.*\\)" url)
                          (match-string-no-properties 1 url)))
               (http (open-network-stream
                      "package-http-process" (current-buffer) host 80)))
          (message "%s" (list host path))
          (process-send-string
           http (concat "GET /" path " HTTP/1.0\r\n\r\n"))
          (message "Retrieving package...")
          (while (eq (process-status http) 'open)
            (sleep-for 1))
          (message "Retrieving package...done")
          (write-region (point-min) (point-max) local-file)))
      (find-file local-file)
      (load (concat ee-ell-install-dir local-file)))))

(defun ee-ell-uninstall (r)
  (interactive)
  ;; TODO
  )

;;; Key Bindings

(defvar ee-ell-keymap nil
  "Local keymap for ee-ell mode.")

(defun ee-ell-keymap-make-default ()
  "Defines default key bindings for `ee-ell-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    (define-key map "\C-o" 'ee-ell-select)
    (define-key map "i" 'ee-ell-mark-install)
    (define-key map "u" 'ee-ell-mark-uninstall)
    (setq ee-ell-keymap map)))

(or ee-ell-keymap
    (ee-ell-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-ell (&optional arg)
  "Browse the categorized Emacs Lisp List."
  (interactive "P")
  (ee-view-buffer-create
   (format "*%s*" ee-ell-mode-name)
   ee-ell-mode-name
   ee-ell-keymap
   ee-ell-data
   nil
   nil
   nil
   "ell.ee"
   t ;; auto-save
   ))

(provide 'ee-ell)

;;; ee-ell.el ends here
