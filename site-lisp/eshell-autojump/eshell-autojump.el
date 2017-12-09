;;; eshell-autojump.el --- autojump command for Eshell
;;
;; Copyright (C) 2013 Alex Schroeder
;;
;; Maintainer: Yen-Chin, Lee <coldnew.tw@gmail.com>

;; Author: Alex Schroeder
;; Kyewords: converience, eshell
;; Version: 0.2
;; X-URL: http://github.com/coldnew/eshell-autojump

;; This program is free software: you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by the Free
;; Software Foundation, either version 3 of the License, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for
;; more details.
;;
;; You should have received a copy of the GNU General Public License along
;; with this program. If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;; [![MELPA](http://melpa.org/packages/eshell-autojump-badge.svg)](http://melpa.org/#/eshell-autojump)
;; [![MELPA Stable](http://stable.melpa.org/packages/eshell-autojump-badge.svg)](http://stable.melpa.org/#/eshell-autojump)


;; Use the command j to list common directories and to jump to them.

;;; Code:

(require 'eshell)

(defcustom eshell-autojump-file
  (expand-file-name "autojump" eshell-directory-name)
  "The name of the file to read/write the directories for autojumping."
  :type 'file
  :group 'eshell-dirs)

(defvar eshell-autojump-map nil
  "Hash map with directories and how often they were called.")

(defun eshell-autojump-load ()
  "Read the initial value of `eshell-autojump-map' from `eshell-autojump-file'.
The file format is a simple alist.
Ignore non-directories."
  (let ((map (make-hash-table :test 'equal)))
    (when (file-exists-p eshell-autojump-file)
      (dolist (element (with-temp-buffer
                         (insert-file eshell-autojump-file)
                         (goto-char (point-min))
                         (read (current-buffer))))
        (when (file-directory-p (car element))
          (puthash (car element) (cdr element) map))))
    (setq eshell-autojump-map map)))

(add-hook 'kill-emacs-hook 'eshell-autojump-save)

(defun eshell-autojump-save ()
  "Save the value of `eshell-autojump-map' to `eshell-autojump-file'.
The file format is a simple alist.
Reduce values by 1% such that eventually unused items fall off the list
after not being used in a hundred sessions."
  (when (and eshell-autojump-file eshell-autojump-map)
    (with-temp-buffer
      (let ((standard-output (current-buffer)))
        (insert "(")
        (maphash (lambda (key value)
                   (when (> value 0)
                     (insert "(")
                     (prin1 key)
                     (insert " . ")
                     (prin1 (- value 0.01))
                     (insert ")\n")))
                 eshell-autojump-map)
        (delete-char -1); eat newline
        (insert ")"))
      (write-file eshell-autojump-file))))

(add-hook 'eshell-directory-change-hook
          'eshell-autojump-record)

(defun eshell-autojump-record ()
  "Record the current directory.
`curdir' is set by `eshell/cd'."
  (unless eshell-autojump-map
    (eshell-autojump-load))
  (let ((curdir default-directory))
    (if (gethash curdir eshell-autojump-map)
        (puthash curdir (1+ (gethash curdir eshell-autojump-map)) eshell-autojump-map)
      (puthash curdir 1 eshell-autojump-map))))

(defun eshell-autojump-candidates ()
  "Return the most popular directories.
Return list of keys sorted by value, descending, from `eshell-autojump-map'."
  (unless eshell-autojump-map
    (eshell-autojump-load))
  (let (keys)
    (maphash (lambda (key value)
               (setq keys (cons key keys)))
             eshell-autojump-map)
    (sort keys (lambda (a b)
                 (> (gethash a eshell-autojump-map)
                    (gethash b eshell-autojump-map))))))

(defun eshell/j (&rest args)           ; all but first ignored
  "Jump to a directory you often cd to.
This compares the argument with the list of directories you usually jump to.
Without an argument, list the ten most common directories.
With a positive integer argument, list the n most common directories.
Otherwise, call `eshell/cd' with the result."
  (setq args (eshell-flatten-list args))
  (let ((path (car args))
        (candidates (eshell-autojump-candidates))
        (case-fold-search (eshell-under-windows-p))
        result)
    (when (not path)
      (setq path 10))
    (if (and (integerp path) (> path 0))
        (progn
          (let ((n (nthcdr (1- path) candidates)))
            (when n
              (setcdr n nil)))
          (eshell-lisp-command (mapconcat 'identity candidates "\n")))
      (while (and candidates (not result))
        (if (string-match path (car candidates))
            (setq result (car candidates))
          (setq candidates (cdr candidates))))
      (eshell/cd result))))

(provide 'eshell-autojump)

;;; eshell-autojump.el ends here
