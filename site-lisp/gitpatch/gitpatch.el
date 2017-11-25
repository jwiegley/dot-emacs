;;; gitpatch.el --- Git-format patch toolkit

;; * Header
;; #+BEGIN_EXAMPLE
;; Copyright (C) 2017 Feng Shu

;; Author: Feng Shu <tumashu@163.com>
;; Homepage: https://github.com/tumashu/gitpatch
;; Keywords: convenience
;; Package-Requires: ((emacs "24.3"))
;; Version: 0.10

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.
;; #+END_EXAMPLE

;;; Commentary:

;; * What is gitpatch                                      :README:
;; Gitpatch is git-format patch toolkit, which let user easy handle
;; git-format patch without exit Emacs.

;; 1. Send patch with `gitpatch-mail'

;;    `gitpatch-mail' can quick send a git-format patch file from magit,
;;    dired or ibuffer buffer.

;; ** Installation

;; 1. Config melpa source, please read: [[http://melpa.org/#/getting-started]]
;; 2. M-x package-install RET gitpatch RET

;; ** Configure

;; #+BEGIN_EXAMPLE
;; (require 'gitpatch)
;; (setq gitpatch-mail-attach-patch-key "C-c i")
;; #+END_EXAMPLE

;; ** Usage
;; *** gitpatch-mail
;; 1. Move the point to the patch-name in magit-status, dired or ibuffer buffer.
;; 2. M-x gitpatch-mail
;; 3. Select an email address as TO Field, if you set `gitpatch-mail-database'.
;; 4. Add another patch with "C-c i" by default (Optional).
;; 5. Edit and send email.

;; NOTE: User can config `gitpatch-mail' in other type buffer with the help of
;; `gitpatch-mail-get-patch-functions'


;;; Code:

;; * gitpatch's code                                                        :code:
(require 'cl-lib)


(defgroup gitpatch nil
  "Utils for Git-format patch file."
  :prefix "gitpatch-"
  :group 'applications)

(defcustom gitpatch-mail-function 'message-mail
  "The function used to compose patch mail.
you can choose `message-mail' or `gnus-msg-mail'."
  :group 'gitpatch
  :type '(choice (const :tag "Message-mode" message-mail)
                 (const :tag "Gnus" gnus-msg-mail)))

(defcustom gitpatch-mail-get-patch-functions
  '(gitpatch-mail-get-patch-from-magit
    gitpatch-mail-get-patch-from-dired
    gitpatch-mail-get-patch-from-ibuffer)
  "A list of function, which used to get git patch file's patch."
  :group 'gitpatch
  :type '(repeat (symbol :tag "Patch-path function")))

(defcustom gitpatch-mail-database nil
  "A list of email address, user can select an email address as TO field."
  :group 'gitpatch
  :type '(choice (const :tag "Disable" nil)
                 (repeat :tag "Add new email address" string)))

(defcustom gitpatch-mail-attach-patch-key nil
  "A key used to attach another patch file to email.
this key string should be recognized by `kbd'."
  :group 'gitpatch
  :type '(choice (const :tag "No keybinding" nil)
                 (string :tag "Keybinding string")))

(defvar-local gitpatch-mail--patch-directory nil)

(defun gitpatch-mail--patch-file-p (file)
  "Test FILE is a patch file."
  (and file (stringp file)
       (file-readable-p file)
       (string-match-p "\\.patch$" file)))

(defun gitpatch-mail--get-patch-file ()
  "Get a git-format patch's full patch."
  (let ((file (or (cl-some (lambda (func)
                             (when (functionp func)
                               (funcall func)))
                           gitpatch-mail-get-patch-functions)
                  (gitpatch-mail-get-patch-from-minibuffer))))
    (unless file
      (message "[Gitpatch]: the selected file is not a patch file."))
    file))

;; Fix compile warn
(defvar magit--default-directory)
(declare-function magit-file-at-point "magit-git.el" nil)
(declare-function dired-file-name-at-point "dired.el" nil)
(declare-function ibuffer-current-buffer "ibuffer.el" (&optional must-be-live))

(defun gitpatch-mail-get-patch-from-magit ()
  "Get a git-format patch's full path from magit buffer."
  (when (eq major-mode 'magit-status-mode)
    (let ((dir magit--default-directory)
          (file-name (magit-file-at-point)))
      (when (and (stringp dir)
                 (stringp file-name))
        (let ((file (concat (file-name-as-directory dir)
                            file-name)))
          (when (gitpatch-mail--patch-file-p file)
            file))))))

(defun gitpatch-mail-get-patch-from-minibuffer ()
  "Get a git-format patch's full path from minibuffer."
  (let ((file (read-file-name "[Gitpatch]: please select a patch: ")))
    (when (gitpatch-mail--patch-file-p file)
      file)))

(defun gitpatch-mail-get-patch-from-dired ()
  "Get a git-format patch's full path from dired buffer."
  (when (eq major-mode 'dired-mode)
    (let ((file (dired-file-name-at-point)))
      (when (gitpatch-mail--patch-file-p file)
        file))))

(defun gitpatch-mail-get-patch-from-ibuffer ()
  "Get a git-format patch's full path from ibuffer buffer."
  (when (eq major-mode 'ibuffer-mode)
    (let ((file (buffer-file-name (ibuffer-current-buffer))))
      (princ file)
      (when (gitpatch-mail--patch-file-p file)
        file))))

(defun gitpatch-mail--extract-subject (patch-file)
  "Extract subject from PATCH-FILE."
  (when (and patch-file
             (stringp patch-file)
             (file-readable-p patch-file))
    (with-temp-buffer
      (insert-file-contents patch-file)
      (goto-char (point-min))
      (buffer-substring-no-properties
       (re-search-forward "^ *Subject: +")
       (line-end-position)))))

;;;###autoload
(defun gitpatch-mail ()
  "Mail a git-format patch file ‘message-mode’ or its derived mode."
  (interactive)
  (let* ((file (gitpatch-mail--get-patch-file))
         (subject (gitpatch-mail--extract-subject file))
         (to (when gitpatch-mail-database
               (if (= (length gitpatch-mail-database) 1)
                   (car gitpatch-mail-database)
                 (completing-read "TO: " gitpatch-mail-database)))))
    (when file
      (funcall gitpatch-mail-function to subject)
      (mml-attach-file file "text/x-patch" subject "inline")
      (setq gitpatch-mail--patch-directory
            (file-name-directory file))
      (when (and gitpatch-mail-attach-patch-key
                 (stringp gitpatch-mail-attach-patch-key))
        (local-set-key (kbd gitpatch-mail-attach-patch-key) 'gitpatch-mail-attach-patch)
        (setq header-line-format
              (format "## Type '%s' to attach another patch ##"
                      gitpatch-mail-attach-patch-key))))))

;;;###autoload
(defun gitpatch-mail-attach-patch ()
  "Attach a patch file to mail.
The patch is in directory `gitpatch-mail--patch-directory'."
  (interactive)
  (let* ((dir gitpatch-mail--patch-directory)
         (file (completing-read "[Gitpatch] please select a patch file:"
                                (directory-files dir t "\\.patch$"))))
    (mml-attach-file file "text/x-patch" nil "inline")))


(provide 'gitpatch)

;; * Footer

;; Local Variables:
;; coding: utf-8-unix
;; End:

;;; gitpatch.el ends here
