;;; magithub-faces.el --- faces of Magithub          -*- lexical-binding: t; -*-

;; Copyright (C) 2017  Sean Allred

;; Author: Sean Allred <code@seanallred.com>
;; Keywords: faces

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

;; Holds all faces for Magithub.

;;; Code:

(require 'faces)
(require 'magit)
(require 'git-commit)

(defface magithub-repo
  '((t :inherit magit-branch-remote))
  "Face used for repository names."
  :group 'magithub-faces)

(defface magithub-issue-title
  '((t))
  "Face used for issue titles."
  :group 'magithub-faces)

(defface magithub-issue-number
  '((t :inherit magit-dimmed))
  "Face used for issue numbers."
  :group 'magithub-faces)

(defface magithub-issue-title-with-note
  '((t :inherit magithub-issue-title :inherit (git-commit-summary)))
  "Face used for issue titles when the issue has an attached note.
See also `magithub-issue-personal-note'."
  :group 'magithub-faces)

(defface magithub-user
  '((t :inherit magit-log-author))
  "Face used for usernames."
  :group 'magithub-faces)

(defface magithub-ci-no-status
  '((t :inherit magit-dimmed))
  "Face used when CI status is `no-status'."
  :group 'magithub-faces)

(defface magithub-ci-error
  '((t :inherit magit-signature-untrusted))
  "Face used when CI status is `error'."
  :group 'magithub-faces)

(defface magithub-ci-pending
  '((t :inherit magit-signature-untrusted))
  "Face used when CI status is `pending'."
  :group 'magithub-faces)

(defface magithub-ci-success
  '((t :inherit success))
  "Face used when CI status is `success'."
  :group 'magithub-faces)

(defface magithub-ci-failure
  '((t :inherit error))
  "Face used when CI status is `failure'"
  :group 'magithub-faces)

(defface magithub-ci-unknown
  '((t :inherit magit-signature-untrusted))
  "Face used when CI status is `unknown'."
  :group 'magithub-faces)

(defface magithub-label '((t :box t))
  "The inherited face used for labels.
Feel free to customize any part of this face, but be aware that
`:foreground' will be overridden by `magithub-label-propertize'."
  :group 'magithub)

(defface magithub-notification-reason
  '((t :inherit magit-dimmed))
  "Face used for notification reasons."
  :group 'magithub-faces)

(defface magithub-deleted-thing
  '((t :background "red4" :inherit magit-section-highlight))
  "Face used for things about to be deleted."
  :group 'magithub-faces)

(provide 'magithub-faces)
;;; magithub-faces.el ends here
