;;; github-pullrequest.el --- Create and fetch Github Pull requests with ease  -*- lexical-binding: t; -*-

;; Copyright (C) 2016  Jakob Lind

;; Author: Jakob Lind <karl.jakob.lind@gmail.com>
;; URL: https://github.com/jakoblind/github-pullrequest
;; Keywords: tools
;; Package-Requires: ((emacs "24.4") (request "0.2.0") (dash "2.11.0") (magit "2.10.0"))
;; Version: 1.0

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

;; Emacs package to smoothly create and checkout Github pull requests.
;; Uses the Github access token for authorization to Github.

;;; Code:

(require 'request)
(require 'dash)
(require 'magit)
(require 'json)

(defun github-pullrequest-name-from-branch (branchname)
  "Create a human readable name from BRANCHNAME."
  (replace-regexp-in-string "-" " " branchname))

(defun github-pullrequest--get-existing-list (accesstoken)
  "Fetch a list of existing pull request from the current Github repo with ACCESSTOKEN to authenticate aginst github."
  (message "Fetching pull requests...")
  (request (concat (github-pullrequest-get-repo-api-base) (concat "pulls?access_token=" accesstoken))
           :type "GET"
           :headers '(("Content-Type" . "application/json"))
           :data  (json-encode
                   (list '("state" . "open")
                         '("sort" . "created")))
           :parser 'json-read
           :error (cl-function (lambda (&rest args &key response data error-thrown &allow-other-keys)
                                 ;; todo throw error here or something
                                 (message "Error creating pull request: %S"
                                        ;(alist-get 'message (elt (assoc-default 'errors (request-response-data response)) 0))
                                          (request-response-data response))))
           :success (cl-function (lambda (&key data response &allow-other-keys)
                                   (github-pullrequest--select-and-checkout
                                    (--group-by (assoc-default "title" it)  (append (cl-map 'vector (lambda (pr) (list
                                                                                                                  (cons "branch" (assoc-default 'ref (assoc-default 'head pr)))
                                                                                                                  (cons "title" (assoc-default 'title pr))
                                                                                                                  (cons "number" (assoc-default 'number pr))))
                                                                                            (request-response-data response)) nil)))))))

(defun github-pullrequest--select-and-checkout (pr-list)
  "Make user select a pull request from PR-LIST and checkout the brach belonging to selected pull request."
  (let* ((selected-header (completing-read "Select a PR to checkout: " (mapcar #'car pr-list)))
         (selected-branch (assoc-default "branch" (-flatten (assoc-default selected-header pr-list)))))
    (magit-fetch "origin" nil)
    (magit-branch selected-branch (concat "origin/" selected-branch))
    (magit-checkout selected-branch)
    (message "Checked out branch %S" selected-branch)))

(defun github-pullrequest-api-new (access-token)
  "Create a Github Pull Request using the current branch as head and master branch as base and ACCESS-TOKEN."
  (progn
    (message "Creating pull request...")
    (request (concat (github-pullrequest-get-repo-api-base) (concat "pulls?access_token=" access-token))
             :type "POST"
             :headers '(("Content-Type" . "application/json"))
             :data  (json-encode
                     (list (cons "title" (github-pullrequest-name-from-branch (magit-get-current-branch)))
                           (cons "head" (magit-get-current-branch))
                           '("base" . "master")))
             :parser 'json-read
             :error (cl-function (lambda (&rest args &key response data error-thrown &allow-other-keys)
                                   (message "Error creating pull request: %S"
                                        ;(alist-get 'message (elt (assoc-default 'errors (request-response-data response)) 0))
                                            (request-response-data response))))
             :success (cl-function (lambda (&key data response &allow-other-keys) (message "A Pull request was created! %S" (assoc-default 'html_url (request-response-data response))))))))



(defun github-pullrequest-get-repo-api-base ()
  "Get the base API URL of the current repository from magit."
  (let ((origin (magit-get "remote" "origin" "url")))
    (concat "https://api.github.com/repos"
            (replace-regexp-in-string ".git$" ""
                                      (cond ((string-match "^http" origin) (replace-regexp-in-string "^https?://github.com" "" origin))
                                            (t (concat "/" (replace-regexp-in-string "^git@github.com:" "" origin))))) "/")))

(defun github-pullrequest-get-access-token ()
  "Fetch the users Github access token, either from input or the current repos git config."
  (let ((token (replace-regexp-in-string "\n" "" (github-pullrequest-run-command "config" "--global" "--get" "github.token"))))
    (if (string= token "")
        (let ((new-token (read-from-minibuffer "Github access-token: ")))
          (github-pullrequest-run-command "config" "--global" "--add" "github.token" new-token)
          new-token)
      token)))

(defun github-pullrequest-run-command (&rest args)
  "Run a git command defined in ARGS."
  (let ((git (executable-find "git")))
    (with-output-to-string
      (apply 'process-file git nil standard-output nil args))))

(defun github-pullrequest-is-validate-state-for-new ()
  "Return t if we are in a valid state to create a PR, return nil otherwise."
  (cond ((string= (magit-get-current-branch) "master")
         (message "You are on master, you can't create a pull request from here") nil)
        ((eq (magit-get-upstream-branch) nil)
         (message "You have not defined an upstream for current branch") nil)
        (t t)))

(defun github-pullrequest-is-validate-state-for-checkout ()
  "Return t if we are in a valid state to checkout a pull request."
  ;;todo if we have edited files which are not commited, fail or ask to stash
  t)

;;;###autoload
(defun github-pullrequest-new ()
  "Create a new pull request."
  (interactive)
  (when (github-pullrequest-is-validate-state-for-new)
    (let ((accesstoken (github-pullrequest-get-access-token)))
      (github-pullrequest-api-new accesstoken))))

;;;###autoload
(defun github-pullrequest-checkout ()
  "List open pull request and have the user select one to checkout."
  (interactive)
  (when (github-pullrequest-is-validate-state-for-checkout)
    (let ((accesstoken (github-pullrequest-get-access-token)))
      (github-pullrequest--get-existing-list accesstoken))))

(provide 'github-pullrequest)
;;; github-pullrequest.el ends here
