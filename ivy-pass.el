;;; ivy-pass.el --- ivy interface for pass -*- lexical-binding: t -*-

;; Author: ecraven
;; URL: https://github.com/ecraven/ivy-pass/
;; Package-Requires: ((emacs "24") (ivy "0.8.0") (password-store "1.6.5"))
;; Version: 0.1
;; Keywords: pass, password, convenience, data

;; This file is not part of GNU Emacs.

;;; License:

;; Licensed under the GPLv3.

;;; Commentary:

;; Quick start:
;; Install, configure and initialize pass according to https://www.passwordstore.org/
;; run M-x ivy-pass
;; The default action is to copy the password to the kill ring.

;; Other actions (accessible with M-o):
;; - edit an entry (e)
;; - delete an entry (d)
;; - add an entry (a)
;; - rename an entry (r)
;; - generate a new entry (g)

;;; Code:
(require 'ivy)
(require 'password-store)

(defvar ivy-pass-map (make-sparse-keymap))

(ivy-set-actions
 'ivy-pass
 '(("e"
    ivy-pass--edit-action
    "edit")
   ("d"
    ivy-pass--delete-action
    "delete")
   ("a"
    ivy-pass--add-action
    "add")
   ("r"
    ivy-pass--rename-action
    "rename")
   ("g"
    ivy-pass--generate-action
    "generate")))

(defun ivy-pass--add-action (key)
  "Ask for a new key based on KEY, then edit it."
  (let ((new-key (read-string "New key: " key)))
    (password-store-edit new-key)))

(defun ivy-pass--generate-action (key)
  "Ask for a new key based on KEY, then generate an entry and password for it.

Default PASSWORD-LENGTH is ‘password-store-password-length’."
  (let ((new-key (read-string "Generate password for new key: " key)))
    (password-store-generate new-key)
    (password-store-edit new-key)))

(defun ivy-pass--edit-action (key)
  "Edit entry for KEY."
  (password-store-edit key))

(defun ivy-pass--delete-action (key)
  "Delete entry for KEY."
  (when (yes-or-no-p (format "Really delete the entry `%s'?" key))
    (password-store-remove key)))

(defun ivy-pass--rename-action (key)
  "Rename entry for KEY."
  (let ((new-name (read-string (format "Rename `%s' to: " key) key)))
    (password-store-rename key new-name)))

(defun ivy-pass--password-action (key)
  "Add password for KEY to kill ring."
  (password-store-copy key))

;;;###autoload
(defun ivy-pass ()
  "Select an entry and copy its password to the kill ring."
  (interactive)
  (ivy-read "Copy password of entry: "
            (password-store-list (password-store-dir))
            :require-match t
            :action #'ivy-pass--password-action
            :keymap ivy-pass-map))

(provide 'ivy-pass)
;;; ivy-pass.el ends here
