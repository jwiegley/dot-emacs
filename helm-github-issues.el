;;; helm-github-issues.el --- github issues viewer with helm interface -*- lexical-binding: t; -*-

;; Copyright (C) 2015 by Syohei YOSHIDA

;; Author: Syohei YOSHIDA <syohex@gmail.com>
;; URL: https://github.com/syohex/emacs-helm-github-issues
;; Version: 0.01
;; Package-Requires: ((helm-core "1.7.7") (gh "1.0"))

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

;;; Code:

(require 'cl-lib)

(require 'helm)
(require 'gh-issues)

(defgroup helm-github-issues nil
  "Github issues with helm interface"
  :group 'tools)

(defcustom helm-github-issues-api
  (gh-issues-api "api" :sync t :cache nil :num-retries 1)
  "Github API"
  :group 'helm-github-issues)

(defvar helm-github-issues-repo-list nil)
(defvar helm-github-issues-repo)

(defun helm-github-issues-default-repo ()
  (with-temp-buffer
    (when (zerop (call-process-shell-command "git remote -v" nil t))
      (goto-char (point-min))
      (when (re-search-forward "github\\.com[/:]?\\([^/]+/.+?\\)\\.git" nil t)
        (match-string-no-properties 1)))))

(defun helm-github-issues-filter-issues (issues state)
  (if (string= state "all")
      issues
    (cl-remove-if-not (lambda (issue)
                        (string= (oref issue state) state)) issues)))

(defcustom helm-github-issues-bookmarks nil
  "Bookmarks of projects"
  :type 'list
  :group 'helm-github-issues)

(defun helm-github-issues-init ()
  (let ((state (if current-prefix-arg
                   (completing-read "Issue type: "
                                    '("all" "open" "close")
                                    nil t nil nil "all")
                 "all")))
    (let ((user-repo (split-string helm-github-issues-repo "/")))
      (cl-assert (= (length user-repo) 2))
      (let* ((user (cl-first user-repo))
             (repo (cl-second user-repo))
             (issues (gh-issues-issue-list helm-github-issues-api user repo)))
        (if (null issues)
            (error "This repo has no issues!!")
          (sort (helm-github-issues-filter-issues (oref issues data) state)
                (lambda (a b)
                  (< (oref a number) (oref b number)))))))))

(defun helm-github-issues-real-to-display (issue)
  (with-slots (number title state) issue
    (format "#%-4d [%s] %s" number state title)))

(defun helm-github-issues-chomp (str)
  (replace-regexp-in-string "\r$" "" str))

(defvar helm-github-issues-headers
  (mapcar (lambda (str)
            (format "%-6s :" (propertize str 'face 'highlight)))
          '("Title" "Number" "User" "Status")))

(defun helm-github-issues-format (title number user state)
  (mapconcat 'identity
             (cl-mapcar (lambda (header value)
                          (format "%s %s" header value))
                        helm-github-issues-headers
                        (list title number user state))
             "\n"))

(defun helm-github-issues-persistent-action (issue)
  (with-current-buffer (get-buffer-create "*Help Github Issues*")
    (erase-buffer)
    (goto-char (point-min))
    (with-slots (title number user state body) issue
      (insert (helm-github-issues-format
               title number (oref user login) state))
      (insert "\n\n")
      (let ((before-body (point)))
        (insert (helm-github-issues-chomp body))
        (fill-region before-body (point-max)))))
  (with-help-window (help-buffer)
    (princ (with-current-buffer "*Help Github Issues*"
             (buffer-string)))))

(defun helm-github-issues-construct-url (url)
  (replace-regexp-in-string
   "api\\." ""
   (replace-regexp-in-string "/repos" "" url)))

(defvar helm-github-issues-source
  (helm-build-sync-source "Github Issues"
    :candidates #'helm-github-issues-init
    :real-to-display #'helm-github-issues-real-to-display
    :persistent-action #'helm-github-issues-persistent-action
    :action (lambda (issue)
              (browse-url (helm-github-issues-construct-url
                           (oref issue url))))))

;;;###autoload
(defun helm-github-issues ()
  (interactive)
  (let ((helm-github-issues-repo (completing-read "Repositry(user/repo): "
                                                  helm-github-issues-bookmarks
                                                  nil nil nil
                                                  helm-github-issues-repo-list
                                                  (helm-github-issues-default-repo))))
    (helm :sources '(helm-github-issues-source) :buffer "*helm github issues*")))

(provide 'helm-github-issues)

;; Local Variables:
;; byte-compile-warnings: (not cl-functions)
;; coding: utf-8
;; indent-tabs-mode: nil
;; End:

;;; helm-github-issues.el ends here
