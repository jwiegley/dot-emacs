;;; magithub-repo.el --- repo tools                  -*- lexical-binding: t; -*-

;; Copyright (C) 2017  Sean Allred

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

;; Basic tools for working with repositories.

;;; Code:

(require 'magit)
(require 'magithub-core)

(defvar-local magithub-repo nil
  "Repo object.")

(defvar magit-magithub-repo-section-map
  (let ((m (make-sparse-keymap)))
    (set-keymap-parent m magithub-map)
    (define-key m [remap magithub-browse-thing] #'magithub-repo-browse)
    m))

(defun magithub-repo-browse (repo)
  (interactive (list (magithub-thing-at-point 'repo)))
  (unless repo
    (user-error "No repository found at point"))
  (let-alist repo
    (browse-url .html_url)))

(defun magithub-repo-data-dir (repo)
  (let-alist repo
    (expand-file-name (format "%s/%s/" .owner.login .name)
                      magithub-dir)))

(provide 'magithub-repo)
;;; magithub-repo.el ends here
