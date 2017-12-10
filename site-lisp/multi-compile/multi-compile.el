;;; multi-compile.el --- Multi target interface to compile. -*- lexical-binding: t; -*-
;;
;; Copyright (C) 2015-2016 Kvashnin Vladimir
;;
;; Author: Kvashnin Vladimir <reangd@gmail.com>
;; Created: 2015-10-01
;; Version: 0.6.0
;; Package-Version: 20160215.1219
;; Keywords: tools compile build
;; URL: https://github.com/ReanGD/emacs-multi-compile
;; Package-Requires: ((emacs "24") (dash "2.12.1"))
;;
;; This file is not part of GNU Emacs.
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.
;;
;;; Commentary:
;; "Multi-compile" is multi target interface to "compile" command.
;;
;; Setup
;; ----
;; M-x package-install multi-compile
;;
;; Configure
;; ----
;;
;; Sample config for Rustlang:
;;  ;;; init.el --- user init file
;;     (require 'multi-compile)
;;     (setq multi-compile-alist '(
;;         (rust-mode . (("rust-debug" . "cargo run")
;;                       ("rust-release" . "cargo run --release")
;;                       ("rust-test" . "cargo test")))
;;         ))
;;
;; In a compilation commands, you can use the templates:
;; - "%path" - "/tmp/prj/file.rs"
;; - "%dir" - "/tmp/prj/"
;; - "%file-name" - "file.rs"
;; - "%file-sans" - "file"
;; - "%file-ext" - "rs"
;; - "%make-dir" - (Look up the directory hierarchy from current file for a directory containing "Makefile") - "/tmp/"
;;
;; for example, add a make compilation (with a template "make-dir"):
;; (setq multi-compile-alist '(
;;     (c++-mode . (("cpp-run" . "make --no-print-directory -C %make-dir")))
;;     (rust-mode . (("rust-debug" . "cargo run")
;;                   ("rust-release" . "cargo run --release")
;;                   ("rust-test" . "cargo test")))
;;     ))
;;
;; You can use filename pattern:
;; (setq multi-compile-alist '(
;;     ("\\.txt\\'" . (("text-filename" . "echo %file-name")))))
;;
;; Or add a pattern for all files:
;; (setq multi-compile-alist '(
;;     ("\\.*" . (("any-file-command" . "echo %file-name")))))
;;
;; You can use different backends for the menu:
;; (setq multi-compile-completion-system 'ido)
;; or
;; (setq multi-compile-completion-system 'helm)
;; or
;; (setq multi-compile-completion-system 'default)
;;
;; Usage
;; ----
;; - Open *.rs file
;; - M-x multi-compile-run
;;
;; For a detailed introduction see:
;; https://github.com/ReanGD/emacs-multi-compile/blob/master/README.md
;;
;;; Code:
(require 'dash)
(require 'compile)

(defgroup multi-compile nil
  "Multi target interface to `compile'."
  :link '(url-link "https://github.com/ReanGD/multi-compile")
  :prefix "multi-compile-"
  :group 'processes)

(defcustom multi-compile-alist
  '(
    (rust-mode . (("rust-debug" . "cargo run")
                  ("rust-release" . "cargo run --release")
                  ("rust-test" . "cargo test")))
    (c++-mode . (("cpp-run" . "make --no-print-directory -C %make-dir")))
    )
  "Alist of filename patterns vs corresponding format control strings."
  :type '(repeat
          (cons
           (choice :tag "Key"
                   (regexp :tag "Filename or buffer pattern")
                   (function :tag "Major-mode")
                   (sexp :tag "Expression")
                   )
           (repeat :tag "Settings"
                   (choice :tag "Type"
                           (cons :tag "Default compilation directory"
                                 (string :tag "Menu item")
                                 (string :tag "Command"))
                           (list :tag "Set compilation directory"
                                 (string :tag "Menu item")
                                 (string :tag "Command")
                                 (sexp :tag "Expression returns a compilation root"))
                           ))))
  :group 'multi-compile)

(defcustom multi-compile-template
  '(
    ("%path" . (buffer-file-name))
    ("%dir" . (file-name-directory (buffer-file-name)))
    ("%file-name" . (file-name-nondirectory (buffer-file-name)))
    ("%file-sans" . (file-name-sans-extension (file-name-nondirectory (buffer-file-name))))
    ("%file-ext" . (file-name-extension (file-name-nondirectory (buffer-file-name))))
    ("%make-dir" . (locate-dominating-file (buffer-file-name) "Makefile"))
    )
  "Default expansion list."
  :type '(alist :key-type string :value-type sexp)
  :group 'multi-compile)

(defcustom multi-compile-completion-system 'ido
  "The completion system to be used by multi-compile."
  :type '(radio
          (const :tag "Ido" ido)
          (const :tag "Helm" helm)
          (const :tag "Default" default)
          (function :tag "Custom function"))
  :group 'multi-compile)

(defcustom multi-compile-history '()
  "Operations history ."
  :type 'list
  :group 'multi-compile)

(defcustom multi-compile-history-length 50
  "The maximum size of the history."
  :type 'integer
  :group 'multi-compile)

(defcustom multi-compile-history-file
  (expand-file-name "multi-compile.cache" user-emacs-directory)
  "The name of multi-compile cache file."
  :type 'string
  :group 'multi-compile)

(defun multi-compile--add-to-history (item)
  "Add ITEM to history and save history to file."
  (setq multi-compile-history
        (-take multi-compile-history-length
               (cons item
                     (-remove-item item multi-compile-history))))
  (when (file-writable-p multi-compile-history-file)
    (with-temp-file multi-compile-history-file
      (insert (let (print-length) (prin1-to-string multi-compile-history)))))
  item)

(defun multi-compile--load-hostory ()
  "Load history from file."
  (with-demoted-errors
      "Error during file deserialization: %S"
      (when (file-exists-p multi-compile-history-file)
        (with-temp-buffer
          (insert-file-contents multi-compile-history-file)
          (setq multi-compile-history (read (buffer-string)))))))

(defun multi-compile--fill-template (format-string)
  "Apply multi-compile-template to FORMAT-STRING."
  (dolist (template multi-compile-template)
    (while (string-match (car template) format-string)
      (let ((new-text (save-match-data (eval (cdr template)))))
        (setq format-string
              (replace-match
               (if new-text new-text
                 (concat "not-found-" (substring (car template) 1)))
               t nil format-string)))))
  format-string)

(defun multi-compile--check-mode (mode-pattern filename)
  "Check that the MODE-PATTERN and the FILENAME match."
  (or
   (and (symbolp mode-pattern)
        (eq mode-pattern major-mode))
   (and (listp mode-pattern)
        (eval-expression mode-pattern))
   (and (stringp mode-pattern)
        (string-match mode-pattern filename))))

(defun multi-compile--fill-command-list (filename)
  "Fill command list from settings for the FILENAME."
  (let ((command-list '()))
    (dolist (mode-item multi-compile-alist)
      (if (multi-compile--check-mode (car mode-item) filename)
          (setq command-list
                (append command-list (cdr mode-item)))
        )
      )
    command-list))

(defun multi-compile--choice-compile-command (compile-list)
  "Choice compile command from COMPILE-LIST."
  (if (= 1 (length compile-list))
      (cdar compile-list)
    (let* ((prompt "action: ")
           (keys (mapcar #'car compile-list))
           (choices (-union (-intersection multi-compile-history keys) keys)))
      (cdr
       (assoc
        (multi-compile--add-to-history
         (cond
          ((eq multi-compile-completion-system 'ido)
           (ido-completing-read prompt choices))
          ((eq multi-compile-completion-system 'default)
           (completing-read prompt choices))
          ((eq multi-compile-completion-system 'helm)
           (if (fboundp 'helm-comp-read)
               (helm-comp-read prompt choices
                               :candidates-in-buffer t
                               :must-match 'confirm)
             (user-error "Please install helm from https://github.com/emacs-helm/helm")))
          (t (funcall multi-compile-completion-system prompt choices))))
        compile-list)))))

(defun multi-compile--get-command-template ()
  "Get command pattern selected by the user."
  (let ((filename (if (stringp buffer-file-name) buffer-file-name (buffer-name))))
    (if (not filename)
        (read-string "Compile command: ")
      (let ((command-list (multi-compile--fill-command-list filename)))
        (if command-list
            (multi-compile--choice-compile-command command-list)
          (read-string "Compile command: "))))))

;;;###autoload
(defun multi-compile-locate-file-dir (name)
  "Look up the directory hierarchy from current file for a directory containing file NAME."
  (locate-dominating-file (buffer-file-name) name))

;;;###autoload
(defun multi-compile-run ()
  "Choice target and start compile."
  (interactive)
  (let* ((template (multi-compile--get-command-template))
         (command (or (car-safe template) template))
         (default-directory (if (listp template) (eval-expression (cadr template)) default-directory)))
    (compilation-start
     (multi-compile--fill-template command))))

(multi-compile--load-hostory)

(provide 'multi-compile)

;;; multi-compile.el ends here
