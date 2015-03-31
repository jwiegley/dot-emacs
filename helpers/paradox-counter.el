;;; paradox-counter.el --- Functions for counting the number of stars on each github emacs package.

;; Copyright (C) 2014 Artur Malabarba <bruce.connor.am@gmail.com>

;; Author: Artur Malabarba <bruce.connor.am@gmail.com>
;; URL: http://github.com/Bruce-Connor/paradox
;; Version: 0.1
;; Prefix: paradox
;; Separator: -
;; Requires: paradox

;;; License:
;;
;; This file is NOT part of GNU Emacs.
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 2
;; of the License, or (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;

;;; Change Log:
;; 0.1 - 2014/04/03 - Generator complete.
;; 0.1 - 2014/04/03 - Created File.
;;; Code:

(require 'paradox-github)
(eval-when-compile (require 'cl))

(defcustom paradox-melpa-directory
  (expand-file-name "~/.melpa/")
  "Directory with melpa package recipes."
  :type 'directory
  :group 'paradox)
(defcustom paradox-download-count-url
  "http://melpa.org/download_counts.json"
  ""
  :type 'string
  :group 'paradox)

(defcustom paradox-recipes-directory
  (when (file-directory-p (concat paradox-melpa-directory "recipes/"))
    (concat paradox-melpa-directory "recipes/"))
  "Directory with melpa package recipes."
  :type 'directory
  :group 'paradox)

(defcustom paradox--star-count-output-file
  (expand-file-name "./star-count")
  "File where a list of star counts will be saved."
  :type 'file
  :group 'paradox-counter
  :package-version '(paradox-counter . "0.1"))
(defcustom paradox--output-data-file
  (expand-file-name "../data")
  "File where a list of star counts will be saved."
  :type 'file
  :group 'paradox-counter
  :package-version '(paradox-counter . "0.1"))

;;;###autoload
(defun paradox-generate-star-count (&optional recipes-dir)
  "Get the number of stars for each github repo and return.
Also saves result to `package-star-count'"
  (interactive)
  (setq paradox-github-token
        (or (getenv "GHTOKEN") paradox-github-token))
  (unless recipes-dir
    (setq recipes-dir paradox-recipes-directory))
  (setq paradox--star-count nil)
  (setq paradox--package-repo-list nil)
  (require 'json)
  (setq paradox--download-count
        (paradox--github-action paradox-download-count-url nil 'json-read))
  (with-temp-buffer
    (let* ((i 0)
           (files (directory-files recipes-dir t "\\`[^\\.]"))
           (N (length files)))
      (dolist (file files)
        (paradox-log "%s / %s" (incf i) N)
        (insert-file-contents file)
        (let ((package (read (buffer-string)))
              repo)
          (when (eq 'github (cadr (memq :fetcher package)))
            (setq repo (cadr (memq :repo package)))
            (push (cons (car package) (paradox-fetch-star-count repo))
                  paradox--star-count)
            (push (cons (car package) repo)
                  paradox--package-repo-list)))
        (erase-buffer))))
  (paradox-list-to-file))

(defun paradox-log (&rest s)
  (princ (concat (apply #'format s) "\n") t))

(defun paradox-error (&rest s)
  (apply #'message s))

(defvar paradox--output-error-file (expand-file-name "~/.invalid-packages-paradox.log")
  "")

(defun paradox-list-to-file ()
  "Save lists in \"data\" file."
  (with-temp-file paradox--output-error-file
    (pp (cl-remove-if #'cdr paradox--star-count)
        (current-buffer)))
  (with-temp-file paradox--output-data-file
    (pp paradox--star-count (current-buffer))
    (pp paradox--package-repo-list (current-buffer))
    (pp paradox--download-count (current-buffer))))

(defun paradox-fetch-star-count (repo)
  (let ((sc (cdr (assq 'stargazers_count
                       (paradox--github-action
                        (format "repos/%s" repo)
                        nil #'json-read)))))
    ;; (unless (numberp sc)
    ;;   (paradox-error "%s	%s" repo sc))
    sc))

(provide 'paradox-counter)
;;; paradox-counter.el ends here.
