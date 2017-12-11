;;; helm-pass.el --- helm interface of pass, the standard Unix password manager -*- lexical-binding: t; -*-

;; Copyright (C) 2016, 2017 J. Alexander Branham

;; Author: J. Alexander Branham <branham@utexas.edu>
;; Maintainer: J. Alexander Branham <branham@utexas.edu>
;; URL: https://github.com/jabranham/helm-pass
;; Version: 0.2
;; Package-Requires: ((helm "0") (password-store "0") (auth-password-store "0"))

;; This file is not part of GNU Emacs.

;;; License:
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see
;; <http://www.gnu.org/licenses/>

;;; Commentary:

;; Emacs helm interface for pass, the standard Unix password manager

;; Users of helm-pass may also be interested in functionality provided by other Emacs packages dealing with pass:
;; password-store.el (which helm-pass relies on): https://git.zx2c4.com/password-store/tree/contrib/emacs/password-store.el
;; pass.el (a major mode for pass): https://github.com/NicolasPetton/pass
;; auth-password-store.el (integration of Emacs' auth-source with pass): https://github.com/DamienCassou/auth-password-store

;; Usage:

;; (require 'helm-pass)
;;

;;; Code:

(require 'helm)
(require 'password-store)
(require 'auth-password-store)

(defgroup helm-pass nil
  "Emacs helm interface for helm-pass"
  :group 'helm)

(defun helm-pass-get-username (entry)
  "Get username for ENTRY.

Does not clear it from clipboard."
  (let ((username (auth-pass-get "user" entry)))
    (if username
        (progn (password-store-clear)
               (kill-new username))
      (message "Username not found!"))))

(defcustom helm-pass-actions
  '(("Copy password to clipboard" . password-store-copy)
    ("Copy username to clipboard" . helm-pass-get-username)
    ("Edit entry" . password-store-edit)
    ("Browse url of entry" . password-store-url))
  "List of actions for helm-pass"
  :group 'helm-pass
  :type '(alist :key-type string :value-type function))

(defvar helm-source-pass
  (helm-build-sync-source "Password File"
    :candidates #'password-store-list
    :action helm-pass-actions))

;;;###autoload
(defun helm-pass ()
  "Helm interface for pass"
  (interactive)
  (helm :sources 'helm-source-pass
        :buffer "*helm-pass*"))

(provide 'helm-pass)
;;; helm-pass.el ends here
