;;; dired-ext.el --- Directory groups and Dired helpers -*- lexical-binding: t; -*-

;; Copyright (C) 2026 John Wiegley
;; Author: John Wiegley <johnw@gnu.org>
;; Keywords: files

;;; Commentary:

;; Bind `dired-ext-open-group' to C-c j, then type a suffix from
;; `dired-ext-directory-groups'.  No RET is needed.  A group shows
;; directories in Dired, or bookmarks at their saved positions.  With
;; C-u, show Magit status instead of Dired.  `dired-ext-two-pane' retains
;; the startup layout.

;;; Code:

(require 'cl-lib)
(require 'dired)
(require 'dired-aux)

(declare-function push-window-configuration "init")
(declare-function bookmark-get-bookmark "bookmark"
                  (bookmark-name-or-record &optional noerror))
(declare-function bookmark-jump "bookmark" (bookmark &optional display-func))
(declare-function bookmark-maybe-load-default-file "bookmark" ())
(declare-function magit-status-setup-buffer "magit-status" (&optional directory))
(declare-function magit-toplevel "magit-git" (&optional directory))
(defvar magit-display-buffer-function)
(defvar ediff-after-quit-hook-internal)

(defgroup dired-ext nil
  "Directory groups and Dired helpers."
  :group 'dired)

(define-widget 'dired-ext-group-item 'lazy
  "A directory or bookmark in a `dired-ext-directory-groups' entry."
  :tag "Item"
  :type '(choice directory
                 (list :tag "Directory" (const directory) directory)
                 (list :tag "Bookmark" (const bookmark) (string :tag "Name"))))

(defcustom dired-ext-directory-groups
  '(("~" "~/")
    ("D" "~/Downloads")
    ("d " "~/Desktop")
    ("dd" "~/Desktop" "~/Downloads")
    ("di" "~/Desktop" "~/Inbox")
    ("j" "~/Desktop" "~/Downloads" "~/Inbox")
    ("e" "~/.config/emacs")
    ("f" (bookmark "Focus"))
    ("n" "~/src/nix")
    ("o" "~/Documents/Obsidian"))
  "Key suffixes and item lists for `dired-ext-open-group'.
Keys are literal strings, not `kbd' notation: \"d \" means d then space.
A key must not be a prefix of another key.

Each group contains one to three items.  An item is a directory name,
or (directory PATH), which means the same; or it is (bookmark NAME),
which shows the buffer and position of the bookmark NAME.

One item fills the frame; two appear left and right.  With three, the
first is lower-left, the second fills the right, and the third is
upper-left.  The right-hand window is selected when present, matching
the original startup layout."
  :type '(alist :key-type (string :tag "Key suffix")
                :value-type (choice
                             (list :tag "One item" dired-ext-group-item)
                             (list :tag "Left / right"
                                   dired-ext-group-item dired-ext-group-item)
                             (list :tag "Lower-left / right / upper-left"
                                   dired-ext-group-item dired-ext-group-item
                                   dired-ext-group-item)))
  :group 'dired-ext)

(defun dired-ext--parse-item (item)
  "Return group ITEM as (directory . PATH) or (bookmark . NAME).
PATH is expanded.  Signal a `user-error' if ITEM is malformed."
  (pcase item
    ((and (or (and (pred stringp) path) `(directory ,path))
          (guard (and (stringp path) (> (length path) 0))))
     (cons 'directory (expand-file-name path)))
    ((and `(bookmark ,name) (guard (and (stringp name) (> (length name) 0))))
     (cons 'bookmark name))
    (_ (user-error "Not a directory or bookmark: %S" item))))

(defun dired-ext--open-items (items &optional magit)
  "Display one to three ITEMS in the usual layout.
Each item is a directory or a bookmark; see `dired-ext-directory-groups'.
With MAGIT non-nil, show Git status instead of Dired for directories;
bookmarks are unaffected.  Each directory must exist, and for Magit must
belong to a Git repository.  Each bookmark must exist."
  (unless (and (proper-list-p items) (<= 1 (length items) 3))
    (user-error "A group must contain one to three directories or bookmarks"))
  (setq items (mapcar #'dired-ext--parse-item items))
  (pcase-dolist (`(,kind . ,target) items)
    (pcase-exhaustive kind
      ('directory
       (unless (file-directory-p target)
         (user-error "Not a directory: %s" target))
       (when magit
         (require 'magit)
         (unless (magit-toplevel target)
           (user-error "Not a Git repository: %s" target))))
      ('bookmark
       (require 'bookmark)
       (bookmark-maybe-load-default-file)
       (unless (bookmark-get-bookmark target 'noerror)
         (user-error "No such bookmark: %s" target)))))
  ;; Prepare (BUFFER . POSITION) pairs before replacing the layout, so visit
  ;; errors leave it intact.  POSITION is nil for directories.
  (let ((entries
         (save-window-excursion
           (mapcar (pcase-lambda (`(,kind . ,target))
                     (pcase-exhaustive kind
                       ('bookmark
                        (bookmark-jump target)
                        (cons (current-buffer) (point)))
                       ('directory
                        (list
                         (if magit
                             (let ((magit-display-buffer-function
                                    (lambda (buffer)
                                      (display-buffer-same-window buffer nil))))
                               (magit-status-setup-buffer
                                (file-name-as-directory target)))
                           (let ((buffer (dired-noselect target)))
                             (with-current-buffer buffer (revert-buffer))
                             buffer))))))
                   items))))
    (cl-flet ((show (window entry)
                (set-window-buffer window (car entry))
                (when (cdr entry) (set-window-point window (cdr entry)))))
      (when (fboundp 'push-window-configuration)
        (push-window-configuration))
      (delete-other-windows)
      (show nil (car entries))
      (when (cdr entries)
        (let ((right (split-window-right)))
          (show right (cadr entries))
          (when (cddr entries)
            (show (split-window-below) (car entries))
            (show nil (caddr entries)))
          (select-window right))))))

;;;###autoload
(defun dired-ext-open-group (key &optional arg)
  "Open the directory group named by KEY in `dired-ext-directory-groups'.
Interactively, read its key suffix without requiring RET.  With prefix
ARG, show Magit status instead of Dired for the group's directories,
keeping the same layout; its bookmarks open as usual."
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
    (dired-ext--open-items (cdr group) arg)))

;;;###autoload
(defun dired-ext-two-pane (&optional arg)
  "Open Inbox above Desktop on the left, with Downloads on the right.
With ARG, show the current directory on the left instead."
  (interactive "P")
  (dired-ext--open-items
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
