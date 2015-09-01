;;; ee-textfile.el --- organize information from text files

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
  (require 'add-log))

;;; Constants

(defconst ee-textfile-mode-name "ee-textfile")

;;; Customizable Variables

(defgroup ee-textfile nil
  "Organize information from text files."
  :prefix "ee-textfile-"
  :group 'ee)

(defgroup ee-textfile-apachelog nil
  "Organize information from Apache log files."
  :prefix "ee-textfile-apachelog-"
  :group 'ee-textfile)

(defcustom ee-textfile-apachelog-combined-format "^\\([-a-zA-z0-9.]+\\) - [-A-Za-z]+ \\[\\([0-9]+\\)/\\([a-zA-Z]+\\)/\\([0-9]+\\):\\(.*\\)\\] \"\\([^\"]*\\)\" \\([0-9]+\\) \\([-0-9]+\\) \"\\([^\"]*\\)\" \"\\([^\"]*\\)\""
  "Apache log combined format regexp."
  :type 'regexp
  :group 'ee-textfile-apachelog)

(defcustom ee-textfile-apachelog-common-format "^\\([-a-zA-z0-9.]+\\) - [-A-Za-z]+ \\[\\([0-9]+\\)/\\([a-zA-Z]+\\)/\\([0-9]+\\):\\(.*\\)\\] \"\\([^\"]*\\)\" \\([0-9]+\\) \\([-0-9]+\\)"
  "Apache log common format regexp."
  :type 'regexp
  :group 'ee-textfile-apachelog)

(defcustom ee-textfile-apachelog-remotehost-filter "^127\.0\.0"
  "Filter out the rows whose field `remote-host' matches this regexp."
  :type 'regexp
  :group 'ee-textfile-apachelog)

(defcustom ee-textfile-apachelog-referer-filter "localhost"
  "Filter out the rows whose field `referer' matches this regexp."
  :type 'regexp
  :group 'ee-textfile-apachelog)

(defgroup ee-textfile-changelog nil
  "Organize information from ChangeLog files."
  :prefix "ee-textfile-changelog-"
  :group 'ee-textfile)

;;; Global Variables

(defvar ee-textfile-changelog-date-regexp "^\\sw.........[0-9:+ ]*"
  "Regexp used to find dates in date lines.")
(defvar ee-textfile-changelog-name-regexp "\\([^<(]+?\\)[ \t]*[(<]\\([A-Za-z0-9_.-]+@[A-Za-z0-9_.-]+\\)[>)]"
    "Regexp used to find author names.")
;; (defvar ee-textfile-changelog-email-regexp "\\([^<(]+?\\)[ \t]*[(<]\\([A-Za-z0-9_.-]+@[A-Za-z0-9_.-]+\\)[>)]"
;;   "Regexp used to find author email addresses.")
(defvar ee-textfile-changelog-file-regexp "^\t\\* \\([^:([\n]+\\)"
  "Regexp used to find file names.")
(defvar ee-textfile-changelog-list-regexp "\\= (\\([^) ,:\n]+\\)" ;; TODO: add other regexps from add-log.el
  "Regexp used to find parenthesized lists of functions or variables.") ; unused now
(defvar ee-textfile-changelog-conditionals-regexp "\\[!?\\([^]\n]+\\)\\]\\(:\\| (\\)"
  "Regexp used to find conditionals of the form `[...]'.") ; unused now
(defvar ee-textfile-changelog-function-regexp "<\\([^>\n]+\\)>\\(:\\| (\\)"
  "Regexp used to find items of the form `<....>'.") ; unused now
(defvar ee-textfile-changelog-acknowledgement-regexp "\\(^\t\\|  \\)\\(From\\|Patch\\(es\\)? by\\|Report\\(ed by\\| from\\)\\|Suggest\\(ed by\\|ion from\\)\\)"
  "Regexp used to find acknowledgments.") ; unused now

;;; Data Description

(defvar ee-textfile-changelog-data
  '[(meta
     (format-version . "0.0.1")
     (view-data-file . "view/changelog.ee")
     (collector . ee-textfile-changelog-data-collect)
     (fields date name email file ())
     (key-fields date name file))])

(defvar ee-textfile-apachelog-data
  '[(meta
     (format-version . "0.0.1")
     (view-data-file . "view/apachelog.ee")
     (collector . ee-textfile-apachelog-data-collect)
     (fields ())
     (key-fields line))])

;;; Data Extraction

(defun ee-textfile-changelog-data-collect (data)
  (let* ((field-names (ee-data-field-names data))
         (new-data
          (ee-data-convert-lists-to-vectors
           (let (res date name email file)
             (with-current-buffer ee-parent-buffer
               (save-excursion
                 (save-restriction
                   (widen)
                   (goto-char (point-min))
                   (while (not (eobp))
                     (cond
                      ((looking-at ee-textfile-changelog-date-regexp)
                       (setq date (match-string-no-properties 0))
                       ;; TODO: hack for old-style date format
                       (if (or (looking-at (concat ee-textfile-changelog-date-regexp
                                                   ee-textfile-changelog-name-regexp))
                               (looking-at (concat ee-textfile-changelog-date-regexp
                                                   ;; hack for wrong name format
                                                   "\\(.+\\)[ \t]*")))
                           (setq name (match-string-no-properties 1)
                                 email (match-string-no-properties 2))))
                      ((looking-at ee-textfile-changelog-file-regexp)
                       (mapc (lambda (elt)
                               (setq file elt
                                     res (cons
                                          (mapcar (lambda (field-name)
                                                    (cond
                                                     ((eq field-name 'date) date)
                                                     ((eq field-name 'name) name)
                                                     ((eq field-name 'email) email)
                                                     ((eq field-name 'file) elt)))
                                                  field-names)
                                          res)))
                             (delete "" (split-string
                                         (match-string-no-properties 1)
                                         "[, ]+")))))
                     (forward-line 1)))))
             (nreverse res)))))
    (aset new-data 0 (aref data 0))
    new-data))

(defun ee-textfile-apachelog-data-collect (data)
  (let ((new-data
         (ee-data-convert-lists-to-vectors
          (let (res)
            (with-current-buffer ee-parent-buffer
              (save-excursion
                (goto-char (point-min))
                (while (not (eobp))
                  (cond
                   ((looking-at ee-textfile-apachelog-combined-format)
                    ;; combined format
                    (setq res (cons
                               (list
                                (list (cons 'remote-host (match-string-no-properties 1))
                                      ;; (cons 'remote-logname (match-string-no-properties 2))
                                      ;; (cons 'remote-user (match-string-no-properties 3))
                                      (cons 'time (list (match-string-no-properties 2) (match-string-no-properties 3) (match-string-no-properties 4) (match-string-no-properties 5)))
                                      (cons 'request (match-string-no-properties 6))
                                      (cons 'status (match-string-no-properties 7))
                                      (cons 'bytes-sent (string-to-int (match-string-no-properties 8)))
                                      (cons 'referer (match-string-no-properties 9))
                                      (cons 'user-agent (match-string-no-properties 10))
                                      (cons 'line (buffer-substring (line-beginning-position) (line-end-position)))))
                               res)))
                   ((looking-at ee-textfile-apachelog-common-format)
                    ;; common format
                    (setq res (cons
                               (list
                                (list (cons 'remote-host (match-string-no-properties 1))
                                      ;; (cons 'remote-logname (match-string-no-properties 2))
                                      ;; (cons 'remote-user (match-string-no-properties 3))
                                      (cons 'time (list (match-string-no-properties 2) (match-string-no-properties 3) (match-string-no-properties 4) (match-string-no-properties 5)))
                                      (cons 'request (match-string-no-properties 6))
                                      (cons 'status (match-string-no-properties 7))
                                      (cons 'bytes-sent (string-to-int (match-string-no-properties 8)))
                                      (cons 'line (buffer-substring (line-beginning-position) (line-end-position)))))
                               res))))
                  (forward-line 1))
                (nreverse res)))))))
    (aset new-data 0 (aref data 0))
    new-data))

;;; Actions

(defun ee-textfile-changelog-select (&optional arg other-window)
  (interactive)
  (let* ((data-getters (ee-data-meta-getters-get-set ee-data))
         (r (ee-view-record-get))
         (name (ee-field 'name r data-getters))
         (date (ee-field 'date r data-getters))
         (file (ee-field 'file r data-getters))
         (parent-buffer ee-parent-buffer))
    (when parent-buffer
      (if other-window (select-window (next-window)))
      (switch-to-buffer parent-buffer)
      (goto-char (point-min))
      (and name date (re-search-forward (concat date ".*" name) nil t)
           file (search-forward (concat "\\*.*" file) nil t))
      ;; (set-window-start nil (point))
      ;; if only display other window, then return back to view buffer
      (if (eq other-window 'display)
          (select-window (next-window))))))

(defun ee-textfile-changelog-select-other-window (&optional arg)
  (interactive)
  (ee-textfile-changelog-select arg t))

(defun ee-textfile-changelog-select-other-window-display (&optional arg)
  (interactive)
  (ee-textfile-changelog-select arg 'display))

(defun ee-textfile-execute (r marks)
  (interactive)
  )

;;; Key Bindings

(defvar ee-textfile-keymap nil
  "Local keymap for ee-textfile mode.")

(defun ee-textfile-keymap-make-default ()
  "Defines default key bindings for `ee-textfile-apachelog-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    (define-key map "o" 'ee-textfile-select-other-window)
    (define-key map "\C-o" 'ee-textfile-select-other-window-display)
    (setq ee-textfile-keymap map)))

(or ee-textfile-keymap
    (ee-textfile-keymap-make-default))

(defvar ee-textfile-changelog-keymap nil
  "Local keymap for ee-textfile-changelog mode.")

(defun ee-textfile-changelog-keymap-make-default ()
  "Defines default key bindings for `ee-textfile-changelog-keymap'.
It inherits key bindings from `ee-textfile-keymap'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    (define-key map "o" 'ee-textfile-changelog-select-other-window)
    (define-key map "\C-o" 'ee-textfile-changelog-select-other-window-display)
    (setq ee-textfile-changelog-keymap map)))

(or ee-textfile-changelog-keymap
    (ee-textfile-changelog-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-textfile-changelog (&optional arg)
  "Organize information from ChangeLog files."
  (interactive "P")
  (require 'add-log)
  (ee-view-buffer-create
   (format "*%s*/%s" ee-textfile-mode-name (buffer-name))
   ee-textfile-mode-name
   ee-textfile-changelog-keymap
   ee-textfile-changelog-data))

;;;###autoload
(defun ee-textfile-apachelog (&optional arg)
  "Organize information from Apache log files."
  (interactive "P")
  (ee-view-buffer-create
   (format "*%s*/%s" ee-textfile-mode-name (buffer-name))
   ee-textfile-mode-name
   ee-textfile-keymap
   ee-textfile-apachelog-data))

(provide 'ee-textfile)

;;; ee-textfile.el ends here
