;;; magithub-user.el --- Inspect users  -*- lexical-binding: t; -*-

;; Copyright (C) 2016-2017  Sean Allred

;; Author: Sean Allred <code@seanallred.com>
;; Keywords: lisp

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

;;; Commentary:

;; Code for dealing with the current users and other users

;;; Code:

(require 'ghub+)
(require 'cl-lib)

(require 'magithub-core)

(defvar magit-magithub-user-section-map
  (let ((m (make-sparse-keymap)))
    (set-keymap-parent m magithub-map)
    (define-key m [remap magit-visit-thing] #'magithub-user-visit)
    (define-key m [remap magithub-browse-thing] #'magithub-user-browse)
    (define-key m "m" #'magithub-user-email)
    m))

(defvar magit-magithub-assignee-section-map
  (let ((m (make-sparse-keymap)))
    (set-keymap-parent m magit-magithub-user-section-map)
    (define-key m "a" #'magithub-assignee-add)
    (define-key m [remap magit-delete-thing] #'magithub-assignee-remove)
    m))

(defun magithub-user-me ()
  "Return the currently-authenticated user."
  (magithub-cache :user-demographics
    `(magithub-request
      (ghubp-get-user))
    :message
    "user object for the currently-authenticated user"))

(defun magithub-user (user)
  "Return the full object for USER."
  (magithub-cache :user-demographics
    `(magithub-request
      (ghubp-get-users-username ',user))))

(defun magithub-assignee--verify-manage ()
  (or (magithub-repo-push-p)
      (user-error "You don't have permission to manage assignees in this repository")))

(defun magithub-assignee-add (issue user)
  (interactive (when (magithub-assignee--verify-manage)
                 (let ((issue (magit-section-parent-value (magit-current-section))))
                   (list issue
                         (magithub-user-choose-assignee
                          "Choose an assignee: "
                          (magithub-issue-repo issue))))))
  (let-alist `((repo . ,(magithub-issue-repo issue))
               (issue . ,issue)
               (user . ,user))
    (if (yes-or-no-p (format "Assign '%s' to %s#%d? "
                             .user.login
                             (magithub-repo-name .repo)
                             .issue.number))
        (prog1 (magithub-request
                (ghubp-post-repos-owner-repo-issues-number-assignees
                 .repo .issue (list .user)))
          (let ((sec (magit-current-section)))
            (magithub-cache-without-cache :issues
              (magit-refresh-buffer))
            (magit-section-show sec)))
      (user-error "Aborted"))))

(defun magithub-assignee-remove (issue user)
  (interactive (when (magithub-assignee--verify-manage)
                 (list (magithub-thing-at-point 'issue)
                       (magithub-thing-at-point 'user))))
  (let-alist `((repo . ,(magithub-issue-repo issue))
               (issue . ,issue)
               (user . ,user))
    (if (yes-or-no-p (format "Remove '%s' from %s#%d? "
                             .user.login
                             (magithub-repo-name .repo)
                             .issue.number))
        (prog1 (magithub-request
                (ghubp-delete-repos-owner-repo-issues-number-assignees .repo .issue (list .user)))
          (magithub-cache-without-cache :issues
            (magit-refresh-buffer)))
      (user-error "Aborted"))))

(defun magithub-user-choose (prompt &optional default-user)
  (let (ret-user new-username)
    (while (not ret-user)
      (setq new-username
            (magit-read-string-ns
             (concat prompt
                     (if new-username (format " ['%s' not found]" new-username)))
             (alist-get 'login default-user)))
      (when-let ((try (condition-case _
                          (magithub-request
                           (ghubp-get-users-username `((login . ,new-username))))
                        (ghub-404 nil))))
        (setq ret-user try)))
    ret-user))

(defun magithub-user-choose-assignee (prompt &optional repo default-user)
  (magithub--completing-read
   prompt
   (magithub-request
    (ghubp-get-repos-owner-repo-assignees repo))
   (lambda (user) (let-alist user .login))
   nil t default-user))

(defalias 'magithub-user-visit #'magithub-user-browse)
(defun magithub-user-browse (user)
  "Open USER on Github."
  (interactive (list (magithub-thing-at-point 'user)))
  (if user
      (browse-url (alist-get 'html_url user))
    (user-error "No user here")))

(defun magithub-user-email (user)
  "Email USER."
  (interactive (list (magithub-thing-at-point 'user)))
  (when (and (string= (alist-get 'login (magithub-user-me))
                      (alist-get 'login user))
             (not (y-or-n-p "Email yourself? ")))
    (user-error "Aborted"))
  (unless user
    (user-error "No user here"))
  (let-alist user
    (unless .email
      (user-error "No email found; target user may be private"))
    (if (y-or-n-p (format "Email @%s at \"%s\"? " .login .email))
        (browse-url (format "mailto:%s" .email))
      (user-error "Aborted"))))

(provide 'magithub-user)
;;; magithub-user.el ends here
