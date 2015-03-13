;;; ee-programs.el --- categorized program menu

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

(defconst ee-programs-mode-name "ee-programs")

;;; Customizable Variables

(defgroup ee-programs nil
  "Categorized program menu."
  :prefix "ee-programs-"
  :group 'ee)

(defcustom ee-programs-debian-menu-dir "/usr/lib/menu"
  "Debian GNU/Linux menu directory name."
  :type 'string
  :group 'ee-programs)

(defcustom ee-programs-windows-start-dir "C:/WINDOWS/Start Menu" ;; "C:/WINDOWS/Kaynnista-valikko"
  "M$Window$ Start-menu directory name."
  :type 'string
  :group 'ee-programs)

;;; Data Description

(defvar ee-programs-data
  '[(meta
     (format-version . "0.0.1")
     (view-data-file . "view/programs.ee")
     (collector . ee-programs-data-collect)
     (fields name category command directory ())
     (key-fields name))])

;;; Data Extraction

(defun ee-programs-data-collect (data)
  (let ((new-data
         (ee-data-convert-lists-to-vectors
          (cond ((eq system-type 'gnu/linux)
                 ;; TODO: other GNU/Linux distributions
                 (if (not (file-exists-p ee-programs-debian-menu-dir))
                     (error "Invalid program directory")
                   (prog2
                       (message "Reading directory %s..."
                                ee-programs-debian-menu-dir)
                       (ee-programs-data-collect-debian
                        (ee-data-field-names data)
                        ee-programs-debian-menu-dir)
                     (message "Reading directory %s...done"
                              ee-programs-debian-menu-dir))))
                ((eq system-type 'windows-nt)
                 (if (not (file-exists-p ee-programs-windows-start-dir))
                     (error "Invalid program directory")
                   (prog2
                       (message "Reading directory %s..."
                                ee-programs-windows-start-dir)
                       (ee-programs-data-collect-windows
                        (ee-data-field-names data)
                        ee-programs-windows-start-dir
                        "")
                     (message "Reading directory %s...done"
                              ee-programs-windows-start-dir))))))))
    (aset new-data 0 (aref data 0))
    new-data))

(defun ee-programs-data-collect-debian (field-names dir)
  (if (file-directory-p dir)
      (mapcan
       (lambda (filename)
         (let ((fullname (concat dir filename)))
           (cond
            ((member filename '("." ".." "README"))
             nil)
            ((file-directory-p fullname)
             (ee-programs-data-collect-debian field-names fullname))
            ((file-exists-p fullname)
             (with-temp-buffer
               (insert-file-contents fullname)
               (let ((p (point))
                     res)
                 (while (< p (point-max))
                   (let ((str (buffer-substring-no-properties
                               p
                               (setq p (or (search-forward "\n?package" nil t)
                                           (point-max))))))
                     (setq res (cons
                                (mapcar
                                 (lambda (field-name)
                                   (cond
                                    ;; TODO: add "description" and "longtitle"
                                    ((eq field-name 'name)
                                     (if (or (string-match "[^g]title=\"\\([^\"]*\\)\"" str)
                                             (string-match "[^g]title=\\([^ \t\n\\]*\\)" str))
                                         (match-string 1 str)))
                                    ((eq field-name 'category)
                                     (if (or (string-match "section=\"\\([^\"]*\\)\"" str)
                                             (string-match "section=\\([^ \t\n\\]*\\)" str))
                                         (match-string 1 str)))
                                    ((eq field-name 'command)
                                     (if (or (string-match "command=\"\\([^\"]*\\)\"" str)
                                             (string-match "command=\\([^ \t\n\\]*\\)" str))
                                         (match-string 1 str)))
                                    ((eq field-name ())
                                     (if (or (string-match "needs=\"\\([^\"]*\\)\"" str)
                                             (string-match "needs=\\([^ \t\n\\]*\\)" str))
                                         (list (cons 'needs (match-string 1 str)))))))
                                 field-names)
                                res))))
                 res))))))
       (directory-files (setq dir (file-name-as-directory dir)) nil nil t))))

(defun ee-programs-data-collect-windows (field-names dir path)
  (if (file-directory-p dir)
      (mapcan
       (lambda (filename)
         (let ((fullname (concat dir filename)))
           (cond
            ((member filename '("." ".."))
             nil)
            ((file-directory-p fullname)
             (ee-programs-data-collect-windows
              field-names fullname (concat path "/" filename)))
            ((and (string-match "\\(.*\\)\\.lnk$" filename)
                  (file-exists-p fullname))
             (let ((name (match-string 1 filename)) ; (substring f 0 (- (length f) 4))
                   command
                   directory)
               (with-temp-buffer
                 (insert-file-contents fullname)
                 (goto-char (point-max))
                 (and (re-search-backward "[A-Za-z]+:\[^\000][^\000]+" nil t)
                      (setq directory (concat (match-string-no-properties 0) "\\")))
                 (goto-char (point-min))
                 (and (re-search-forward "[A-Za-z]+:\[^\000][^\000]+" nil t)
                      (setq command (match-string-no-properties 0))
                      (list (mapcar (lambda (field-name)
                                      (cond
                                       ((eq field-name 'name) name)
                                       ((eq field-name 'category) path)
                                       ((eq field-name 'command) command)
                                       ((eq field-name 'directory) directory)))
                                    field-names)))))))))
       (directory-files (setq dir (file-name-as-directory dir)) nil nil t))))

(defun ee-programs-data-file ()
  (cond ((eq system-type 'gnu/linux)
         "programs-debian.ee")
        ((eq system-type 'windows-nt)
         "programs-windows.ee")))

;;; Actions

(defun ee-programs-start-process (&optional arg)
  (interactive)
  (ee-field-set 'read t)
  (ee-view-update '(read)) ;; (ee-view-record-update)
  (let* ((directory (ee-field 'directory))
         (default-directory (if (and directory (file-directory-p directory))
                                directory
                              default-directory)))
    (apply
     'start-process
     (ee-field 'name)
     nil ;; (generate-new-buffer (format "*%s*/%s" ee-programs-mode-name (ee-field 'name)))
     (cond
      ((and (eq system-type 'gnu/linux)
            (equal (ee-field 'needs) "text"))
       (list
        "x-terminal-emulator"
        "-T" (ee-field 'name)
        "-e" (ee-field 'command)))
      ((and (eq system-type 'windows-nt) (fboundp 'w32-shell-name))
       (list (w32-shell-name) "-c" (shell-quote-argument (ee-field 'command))))
      (t
       (split-string (ee-field 'command))))))
  (switch-to-buffer ee-parent-buffer))

;;; Key Bindings

(defvar ee-programs-keymap nil
  "Local keymap for ee-programs mode.")

(defun ee-programs-keymap-make-default ()
  "Defines default key bindings for `ee-programs-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    ;; (define-key map "\C-o" 'ee-programs-start-process)
    (setq ee-programs-keymap map)))

(or ee-programs-keymap
    (ee-programs-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-programs (&optional arg)
  "Categorized program menu."
  (interactive "P")
  (ee-view-buffer-create
   (format "*%s*" ee-programs-mode-name)
   ee-programs-mode-name
   ee-programs-keymap
   ee-programs-data
   nil
   nil
   nil
   (ee-programs-data-file)))

(provide 'ee-programs)

;;; ee-programs.el ends here
