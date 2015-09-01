;;; git-annex.el --- Mode for easy editing of git-annex'd files

;; Copyright (C) 2012 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 20 Oct 2012
;; Version: 1.0
;; Keywords: files data git annex
;; X-URL: https://github.com/jwiegley/git-annex-el

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; Typing C-x C-q in an annexed file buffer causes Emacs to run "git annex
;; edit".  When the buffer is killed Emacs will run "git annex add && git
;; commit -m Updated".
;;
;; Dired has been extended to not show Annex symlinks, but instead to color
;; annexed files green (and preserve the "l" in the file modes).  You have the
;; following commands available in dired-mode on all marked files (or the
;; current file):
;;
;;     @ a    Add file to Git annex
;;     @ e    Edit an annexed file

(eval-when-compile
  (require 'dired nil t)	      ; for variable dired-mode-map
  (require 'dired-aux nil t)	      ; for function dired-relist-file
  (require 'cl))

(defgroup git-annex nil
  "Mode for easy editing of git-annex'd files"
  :group 'files)

(defsubst git-annex (&rest args)
  (apply #'call-process "git" nil nil nil "annex" args))

(defun git-annex-add-file ()
  (git-annex "add" (file-relative-name buffer-file-name default-directory))
  (call-process "git" nil nil nil "commit" "-m" "Updated"))

(defadvice toggle-read-only (before git-annex-edit-file activate)
  (when (and buffer-file-name buffer-read-only
             (file-symlink-p buffer-file-name))
    (let ((target (nth 0 (file-attributes buffer-file-name))))
      (assert (stringp target))
      (when (string-match "\\.git/annex/" target)
        (call-process "git" nil nil nil "annex" "edit"
                      (file-relative-name buffer-file-name default-directory))
        (let ((here (point-marker)))
          (unwind-protect
              (revert-buffer nil t t)
            (goto-char here)))
        (add-hook 'kill-buffer-hook 'git-annex-add-file nil t)
        (setq buffer-read-only t))))
  (when (and buffer-file-name (not buffer-read-only)
             (not (file-symlink-p buffer-file-name)))
    (let ((cur (current-buffer))
          (name buffer-file-name)
          (result))
     (with-temp-buffer
       (call-process "git" nil t nil "diff-files" "--diff-filter=T" "-G^[./]*\\.git/annex/objects/" "--name-only" "--" (file-relative-name name default-directory))
       (setq result (buffer-string)))
     (unless (string= result "")
       (git-annex-add-file)
       (let ((here (point-marker)))
         (unwind-protect
              (revert-buffer nil t t)
           (goto-char here)))
       (setq buffer-read-only nil)))))

(defface git-annex-dired-annexed-available
  '((((class color) (background dark))
     (:foreground "dark green"))
    (((class color) (background light))
     (:foreground "dark green")))
  "Face used to highlight git-annex'd files."
  :group 'git-annex)

(defface git-annex-dired-annexed-unavailable
  '((((class color) (background dark))
     (:foreground "firebrick"))
    (((class color) (background light))
     (:foreground "firebrick")))
  "Face used to highlight git-annex'd files."
  :group 'git-annex)

(defvar git-annex-dired-annexed-available 'git-annex-dired-annexed-available
  "Face name used to highlight available git-annex'd files.")
(defvar git-annex-dired-annexed-unavailable 'git-annex-dired-annexed-unavailable
  "Face name used to highlight unavailable git-annex'd files.")
(defvar git-annex-dired-annexed-invisible
  '(face git-annex-dired-annexed-available invisible t)
  "Face name used to hide a git-annex'd file's annex path.")

(defun git-annex-lookup-file (limit)
  (and (re-search-forward " -> \\(.*\\.git/annex/.+\\)" limit t)
       (file-exists-p
        (expand-file-name (match-string 1) (dired-current-directory)))))

(eval-after-load "dired"
  '(progn
     (add-to-list 'dired-font-lock-keywords
                  (list " -> .*\\.git/annex/"
                        '("\\(.+\\)\\( -> .+\\)" (dired-move-to-filename) nil
                          (1 git-annex-dired-annexed-unavailable)
                          (2 git-annex-dired-annexed-invisible))))
     (add-to-list 'dired-font-lock-keywords
                  (list 'git-annex-lookup-file
                        '("\\(.+\\)\\( -> .+\\)" (dired-move-to-filename) nil
                          (1 git-annex-dired-annexed-available)
                          (2 git-annex-dired-annexed-invisible))))))

(defvar git-annex-dired-map
  (let ((map (make-keymap)))
    (define-key map "a" 'git-annex-dired-add-files)
    (define-key map "d" 'git-annex-dired-drop-files)
    (define-key map "e" 'git-annex-dired-edit-files)
    (define-key map "g" 'git-annex-dired-get-files)
    map)
  "Git-annex keymap for `dired-mode' buffers.")

(add-hook 'dired-mode-hook
          (lambda () (define-key dired-mode-map "@" git-annex-dired-map)))

(defun git-annex-dired--apply (command file-list)
  (let ((here (point)))
    (unwind-protect
        (mapc #'(lambda (file)
                  (git-annex command file)
                  (dired-relist-file (expand-file-name file)))
              file-list)
      (goto-char here))))

(defmacro git-annex-dired-do-to-files (cmd msg &optional commit-after)
  `(defun ,(intern (concat "git-annex-dired-" cmd "-files"))
     (file-list &optional arg)
     (interactive
      (let ((files (dired-get-marked-files t current-prefix-arg)))
        (list files current-prefix-arg)))
     (git-annex-dired--apply ,cmd file-list)
     (let ((msg (format ,msg (length file-list))))
       ,(if commit-after
            `(call-process "git" nil nil nil "commit" "-m" msg))
       (message msg))))

(git-annex-dired-do-to-files "add" "Annex: updated %d file(s)" t)
(git-annex-dired-do-to-files "drop" "Annex: dropped %d file(s)")
(git-annex-dired-do-to-files "edit" "Annex: unlocked %d file(s) for editing")
(git-annex-dired-do-to-files "get" "Annex: got %d file(s)")

(provide 'git-annex)

;;; git-annex.el ends here
