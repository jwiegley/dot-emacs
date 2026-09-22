;;; dired-ext.el --- Directory groups and Dired helpers -*- lexical-binding: t; -*-

;; Copyright (C) 2026 John Wiegley
;; Author: John Wiegley <johnw@gnu.org>
;; Keywords: files

;;; Commentary:

;; Bind `dired-ext-open-group' to C-c j, then type a suffix from
;; `dired-ext-directory-groups'.  No RET is needed.  With C-u, show Magit
;; status instead of Dired.  `dired-ext-two-pane' retains the startup layout.

;;; Code:

(require 'cl-lib)
(require 'dired)
(require 'dired-aux)

(declare-function push-window-configuration "init")
(declare-function magit-status-setup-buffer "magit-status" (&optional directory))
(declare-function magit-toplevel "magit-git" (&optional directory))
(defvar magit-display-buffer-function)
(defvar ediff-after-quit-hook-internal)

(defgroup dired-ext nil
  "Directory groups and Dired helpers."
  :group 'dired)

(defcustom dired-ext-directory-groups
  '(("dD" "~/Desktop" "~/Downloads")
    ("D" "~/Downloads")
    ("ddI" "~/Desktop" "~/Downloads" "~/Inbox")
    ("d " "~/Desktop")
    ("n" "~/src/nix")
    ("e" "~/.config/emacs")
    ("o" "~/Documents/Obsidian"))
  "Key suffixes and directory lists for `dired-ext-open-group'.
Keys are literal strings, not `kbd' notation: \"d \" means d then space.
A key must not be a prefix of another key.

Each group contains one to three directories.  One fills the frame;
two appear left and right.  With three, the first is lower-left, the
second fills the right, and the third is upper-left.  The right-hand
window is selected when present, matching the original startup layout."
  :type '(alist :key-type (string :tag "Key suffix")
                :value-type (choice
                             (list :tag "One directory" directory)
                             (list :tag "Left / right" directory directory)
                             (list :tag "Lower-left / right / upper-left"
                                   directory directory directory)))
  :group 'dired-ext)

(defun dired-ext--open-directories (directories &optional magit)
  "Display one to three DIRECTORIES in the usual layout.
With MAGIT non-nil, show Git status instead of Dired.  Each directory
must exist, and for Magit must belong to a Git repository."
  (unless (and (proper-list-p directories) (<= 1 (length directories) 3)
               (cl-every (lambda (dir) (and (stringp dir) (> (length dir) 0)))
                         directories))
    (user-error "A directory group must contain one to three directory names"))
  (setq directories (mapcar #'expand-file-name directories))
  (when magit (require 'magit))
  (dolist (directory directories)
    (unless (file-directory-p directory)
      (user-error "Not a directory: %s" directory))
    (when (and magit (not (magit-toplevel directory)))
      (user-error "Not a Git repository: %s" directory)))
  ;; Prepare buffers before replacing the layout, so visit errors leave it intact.
  (let ((buffers
         (save-window-excursion
           (mapcar (lambda (directory)
                     (if magit
                         (let ((magit-display-buffer-function
                                (lambda (buffer)
                                  (display-buffer-same-window buffer nil))))
                           (magit-status-setup-buffer
                            (file-name-as-directory directory)))
                       (let ((buffer (dired-noselect directory)))
                         (with-current-buffer buffer (revert-buffer))
                         buffer)))
                   directories))))
    (when (fboundp 'push-window-configuration)
      (push-window-configuration))
    (delete-other-windows)
    (set-window-buffer nil (car buffers))
    (when (cdr buffers)
      (let ((right (split-window-right)))
        (set-window-buffer right (cadr buffers))
        (when (cddr buffers)
          (set-window-buffer (split-window-below) (car buffers))
          (set-window-buffer nil (caddr buffers)))
        (select-window right)))))

;;;###autoload
(defun dired-ext-open-group (key &optional arg)
  "Open the directory group named by KEY in `dired-ext-directory-groups'.
Interactively, read its key suffix without requiring RET.  With prefix
ARG, show Magit status instead of Dired, keeping the same layout."
  (interactive
   (list (let ((map (make-sparse-keymap)))
           (dolist (group dired-ext-directory-groups)
             (define-key map (car group) #'ignore))
           (let ((overriding-terminal-local-map map))
             (read-key-sequence
              (format "Directory group (%s): "
                      (mapconcat (lambda (group) (key-description (car group)))
                                 dired-ext-directory-groups ", ")))))
         current-prefix-arg))
  (when (cl-find ?\C-g key) (keyboard-quit))
  (let ((group (assoc key dired-ext-directory-groups)))
    (unless group
      (user-error "Unknown directory group: %s" (key-description key)))
    (dired-ext--open-directories (cdr group) arg)))

;;;###autoload
(defun dired-ext-two-pane (&optional arg)
  "Open Inbox above Desktop on the left, with Downloads on the right.
With ARG, show the current directory on the left instead."
  (interactive "P")
  (dired-ext--open-directories
   (if arg (list default-directory "~/Downloads")
     '("~/Desktop" "~/Downloads" "~/Inbox"))))

;;;###autoload
(defun dired-ext-next-window ()
  "Select the next Dired window, if any."
  (interactive)
  (let ((next (cl-find-if
               (lambda (window)
                 (with-current-buffer (window-buffer window)
                   (eq major-mode 'dired-mode)))
               (cdr (window-list)))))
    (when next (select-window next))))

;;;###autoload
(defun dired-ext-ediff-files ()
  "Compare the marked files, prompting for a second file if needed."
  (interactive)
  (let ((files (dired-get-marked-files))
        (windows (current-window-configuration)))
    (when (> (length files) 2)
      (user-error "No more than two files should be marked"))
    (let ((file1 (car files))
          (file2 (or (cadr files)
                     (read-file-name "File: " (dired-dwim-target-directory)))))
      (if (file-newer-than-file-p file1 file2)
          (ediff-files file2 file1)
        (ediff-files file1 file2))
      (add-hook 'ediff-after-quit-hook-internal
                (lambda ()
                  (setq ediff-after-quit-hook-internal nil)
                  (set-window-configuration windows))))))

(provide 'dired-ext)
;;; dired-ext.el ends here
