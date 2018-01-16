;;; ghub+.el --- a thick GitHub API client built on ghub  -*- lexical-binding: t; -*-

;; Copyright (C) 2017  Sean Allred

;; Author: Sean Allred <code@seanallred.com>
;; Keywords: extensions, multimedia, tools
;; Homepage: https://github.com/vermiculus/ghub-plus
;; Package-Requires: ((emacs "25") (ghub "1.2") (apiwrap "0.4"))
;; Package-Version: 0.2.1

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

;; Provides some sugar for `ghub'.  See package `apiwrap' for
;; generated function usage instructions.

;;; Code:

(require 'url)
(require 'cl-lib)
(require 'ghub)
(require 'apiwrap)

(eval-and-compile
  (defun ghubp--make-link (alist)
    "Create a link from an ALIST of API endpoint properties."
    (format "https://developer.github.com/v3/%s" (alist-get 'link alist)))

  (defun ghubp--stringify-params (params)
    "Process PARAMS from textual data to Lisp structures."
    (mapcar (lambda (p)
              (if (listp p)
		  (let ((k (car p)) (v (cdr p)))
		    (cons k (alist-get v '((t . "true") (nil . "false")) v)))
		p))
            params))

  (defun ghubp--pre-process-params (params)
    (ghubp--stringify-params params))

  (defvar ghubp-contextualize-function nil
    "Function to contextualize `ghub' requests.
Can return an alist with any of the following properties:

* `auth'
* `headers'
* `host'
* `unpaginate'
* `username'

If (and only if) these properties are non-nil, they will provide
values for the eponymous `ghub-request' keyword arguments.

The function should be callable with no arguments.

See also `ghubp-get-context'.")

  (defvar ghubp-request-override-function nil
    "Function to use instead of `ghub-request' for base calls.
It is expected to have the same signature as `ghub-request'.")

  (defun ghubp-get-context ()
    "Get the current context with `ghubp-contextualize-function'."
    (when (functionp ghubp-contextualize-function)
      (funcall ghubp-contextualize-function)))

  (defun ghubp-get-in-all (props object-list)
    "Follow property-path PROPS in OBJECT-LIST.
Returns a list of the property-values."
    (declare (indent 1))
    (if (or (null props) (not (consp props)))
        object-list
      (ghubp-get-in-all (cdr props)
        (mapcar (lambda (o) (alist-get (car props) o))
                object-list))))

  (defun ghubp-request (method resource params data)
    "Using METHOD, get RESOURCE with PARAMS and DATA.

`ghubp-contextualize-function' is used to contextualize this
request.

If non-nil, `ghubp-request-override-function' is used instead of
`ghub-request'.

METHOD is one of `get', `put', `post', `head', `patch', and
`delete'.

RESOURCE is a string.

PARAMS is a plist.

DATA is an alist."
    (let-alist (ghubp-get-context)
      (let ((method (encode-coding-string (upcase (symbol-name method)) 'utf-8))
            (params (apiwrap-plist->alist params)))
        (funcall (or ghubp-request-override-function
                     #'ghub-request)
                 method resource nil
                 :query params
                 :payload data
                 :unpaginate .unpaginate
                 :headers .headers
                 :username .username
                 :auth .auth
                 :host .host))))

  (apiwrap-new-backend "GitHub" "ghubp"
    '((repo . "REPO is a repository alist of the form returned by `ghubp-get-user-repos'.")
      (org  . "ORG is an organization alist of the form returned by `ghubp-get-user-orgs'.")
      (thread . "THREAD is a thread object of the form returned by `ghubp-get-repos-owner-repo-comments'.")
      (issue . "ISSUE is an issue object of the form returned by `ghubp-get-issues'.")
      (pull-request . "PULL-REQUEST is a pull request object of the form returned by `ghubp-get-repos-owner-repo-pulls'.")
      (review . "REVIEW is a review object of the form returned by `ghubp-get-repos-owner-repo-pulls-number-reviews'.")
      (label . "LABEL is a label object of the form returned by `ghubp-get-repos-owner-repo-issues-number-labels'.")
      (ref . "REF is a string and can be a SHA, a branch name, or a tag name.")
      (milestone . "MILESTONE is a milestone object.")
      (user . "USER is a user object.")
      (user-1 . "USER-1 is a user object.")
      (user-2 . "USER-2 is a user object.")
      (key . "KEY is a key object."))
    :request #'ghubp-request
    :link #'ghubp--make-link
    :pre-process-params #'ghubp--pre-process-params))


;;; Utilities:

(defmacro ghubp-unpaginate (&rest body)
  "Unpaginate API responses while executing BODY."
  `(ghubp-override-context unpaginate t ,@body))

(defmacro ghubp-override-context (context new-value &rest body)
  "Execute body while manually overriding CONTEXT with NEW-VALUE.
NEW-VALUE takes precedence over anything that
`ghubp-contextualize-function' provides for CONTEXT, but
`ghubp-contextualize-function' is otherwise respected."
  (declare (indent 2))
  (unless (memq context '(host auth username unpaginate headers))
    (error (concat "`ghubp-override-context' should only override one "
                   "of the symbols from `ghubp-contextualize-function'.")))
  (let ((sym-other-context (cl-gensym)))
    `(let ((,sym-other-context (ghubp-get-context))
           ghubp-contextualize-function)
       ;; override any existing value for CONTEXT
       (push (cons ',context ,new-value) ,sym-other-context)
       ;; and box the whole thing back into the var
       (setq ghubp-contextualize-function (lambda () ,sym-other-context))
       ,@body)))

(defun ghubp-keep-only (structure object)
  "Keep a specific STRUCTURE in OBJECT.
See URL `http://emacs.stackexchange.com/a/31050/2264'."
  (declare (indent 1))
  (if (and (consp object) (consp (car object)) (consp (caar object)))
      (mapcar (apply-partially #'ghubp-keep-only structure) object)
    (mapcar (lambda (el)
              (if (consp el)
                  (cons (car el)
                        (ghubp-keep-only (cdr el) (alist-get (car el) object)))
                (cons el (alist-get el object))))
            structure)))

(defun ghubp-header (header)
  "Get the value of HEADER from the last request as a string."
  (cdr (assoc-string header ghub-response-headers)))

(defun ghubp-ratelimit-reset-time ()
  "Get the reset time for the rate-limit as a time object."
  (declare (obsolete 'ghubp-ratelimit "2017-10-17"))
  (alist-get 'reset (ghubp-ratelimit)))

(defun ghubp-ratelimit-remaining ()
  "Get the remaining number of requests available."
  (declare (obsolete 'ghubp-ratelimit "2017-10-17"))
  (alist-get 'remaining (ghubp-ratelimit)))

(defun ghubp-ratelimit ()
  "Get `/rate_limit.rate' using `ghub-response-headers'.
Returns nil if the service is not rate-limited.  Otherwise,
returns an alist with the following properties:

  `.limit'
     number of requests we're allowed to make per hour.

  `.remaining'
     number of requests remaining for this hour.

  `.reset'
     time value of instant `.remaining' resets to `.limit'."
  (when (and ghub-response-headers
             (assoc-string "X-RateLimit-Limit" ghub-response-headers))
    (let* ((headers (list "X-RateLimit-Limit" "X-RateLimit-Remaining" "X-RateLimit-Reset"))
           (headers (mapcar (lambda (x) (string-to-number (ghubp-header x))) headers)))
      `((limit     . ,(nth 0 headers))
        (remaining . ,(nth 1 headers))
        (reset     . ,(seconds-to-time
                       (nth 2 headers)))))))

(defun ghubp--follow (method resource &optional params data)
  "Using METHOD, follow the RESOURCE link with PARAMS and DATA.
This method is intended for use with callbacks."
  (let ((url (url-generic-parse-url resource)))
    (when (fboundp 'ghub--host)
      (unless (string-equal (url-host url) (ghub--host))
        (error "Bad link")))
    (ghubp-request method (url-filename url) params data)))

(defun ghubp-follow-get    (resource &optional params data)
  "GET wrapper for `ghubp-follow'."
  (ghubp--follow 'get    resource params data))
(defun ghubp-follow-put    (resource &optional params data)
  "PUT wrapper for `ghubp-follow'."
  (ghubp--follow 'put    resource params data))
(defun ghubp-follow-head   (resource &optional params data)
  "HEAD wrapper for `ghubp-follow'."
  (ghubp--follow 'head   resource params data))
(defun ghubp-follow-post   (resource &optional params data)
  "POST wrapper for `ghubp-follow'."
  (ghubp--follow 'post   resource params data))
(defun ghubp-follow-patch  (resource &optional params data)
  "PATCH wrapper for `ghubp-follow'."
  (ghubp--follow 'patch  resource params data))
(defun ghubp-follow-delete (resource &optional params data)
  "DELETE wrapper for `ghubp-follow'."
  (ghubp--follow 'delete resource params data))

(defun ghubp-base-html-url ()
  "Get the base HTML URL from `ghub-default-host'"
  (if-let ((host (magit-get "github" "host")))
      (and (string-match (rx bos (group (* any)) "/api/v3" eos) host)
           (match-string 1 host))
    "https://github.com"))

(defun ghubp-host ()
  "Exposes `ghub--host'."
  (ghub--host))

(defun ghubp-username ()
  "Exposes `ghub--username'."
  (ghub--username (ghub--host)))

(defun ghubp-token (package)
  "Exposes `ghub--token' in a friendly way."
  (let* ((host (ghub--host))
         (user (ghub--username host)))
    (ghub--token host user package t)))


;;; Issues:

(defapiget-ghubp "/issues"
  "List all issues assigned to the authenticated user across all
visible repositories including owned repositories, member
repositories, and organization repositories."
  "issues/#list-issues")

(defapiget-ghubp "/user/issues"
  "List all issues across owned and member repositories assigned
to the authenticated user."
  "issues/#list-issues")

(defapiget-ghubp "/orgs/:org/issues"
  "List all issues for a given organization assigned to the
authenticated user."
  "issues/#list-issues"
  (org) "/org/:org.login/issues")

(defapiget-ghubp "/repos/:owner/:repo/issues"
  "List issues for a repository."
  "issues/#list-issues-for-a-repository"
  (repo) "/repos/:repo.owner.login/:repo.name/issues")

(defapiget-ghubp "/repos/:owner/:repo/issues/:number"
  "Get a single issue."
  "issues/#get-a-single-issue"
  (repo issue) "/repos/:repo.owner.login/:repo.name/issues/:issue.number")

(defapipost-ghubp "/repos/:owner/:repo/issues"
  "Create an issue.
Any user with pull access to a repository can create an issue."
  "issues/#create-an-issue"
  (repo) "/repos/:repo.owner.login/:repo.name/issues")

(defapipatch-ghubp "/repos/:owner/:repo/issues/:number"
  "Edit an issue.
Issue owners and users with push access can edit an issue."
  "issues/#edit-an-issue"
  (repo issue) "/repos/:repo.owner.login/:repo.name/issues/:issue.number")

(defapiput-ghubp "/repos/:owner/:repo/issues/:number/lock"
  "Lock an issue.
Users with push access can lock an issue's conversation."
  "issues/#lock-an-issue"
  (repo issue) "/repos/:repo.owner.login/:repo.name/issues/:issue.number")

(defapidelete-ghubp "/repos/:owner/:repo/issues/:number/lock"
  "Unlock an issue
Users with push access can unlock an issue's conversation."
  "issues/#unlock-an-issue"
  (repo issue) "/repos/:repo.owner.login/:repo.name/issues/:issue.number")


;;; Issue Assignees:

(defapiget-ghubp "/repos/:owner/:repo/assignees"
  "List assignees.
This call lists all the available assignees to which issues may
be assigned."
  "issues/assignees/#list-assignees"
  (repo) "/repos/:repo.owner.login/:repo.name/assignees")

(defapiget-ghubp "/repos/:owner/:repo/assignees/:assignee"
  ;; todo: sugar to handle valid 404 response
  "Check assignee.
You may also check to see if a particular user is an assignee for
a repository."
  "issues/assignees/#check-assignee"
  (repo user) "/repos/:repo.owner.login/:repo.name/assignees/:user.login")

(defapipost-ghubp "/repos/:owner/:repo/issues/:number/assignees"
  "Add assignees to an Issue.
This call adds the users passed in the assignees key (as their
logins) to the issue."
  "issues/assignees/#add-assignees-to-an-issue"
  (repo issue) "/repos/:repo.owner.login/:repo.name/issues/:issue.number/assignees"
  :pre-process-data
  (lambda (users)
    `((assignees . ,(ghubp-get-in-all '(login) users)))))

(defapidelete-ghubp "/repos/:owner/:repo/issues/:number/assignees"
  "Remove assignees from an Issue.
This call removes the users passed in the assignees key (as their
logins) from the issue."
  "issues/assignees/#remove-assignees-from-an-issue"
  (repo issue) "/repos/:repo.owner.login/:repo.name/issues/:issue.number/assignees"
  :pre-process-data
  (lambda (users)
    `((assignees . ,(ghubp-get-in-all '(login) users)))))


;;; Issue Comments:

(defapiget-ghubp "/repos/:owner/:repo/issues/:number/comments"
  "List comments on an issue.
Issue Comments are ordered by ascending ID."
  "issues/comments/#list-comments-on-an-issue"
  (repo issue) "/repos/:repo.owner.login/:repo.name/issues/:issue.number/comments")

(defapiget-ghubp "/repos/:owner/:repo/issues/comments"
  "List comments in a repository.
By default, Issue Comments are ordered by ascending ID."
  "issues/comments/#list-comments-in-a-repository"
  (repo) "/repos/:repo.owner.login/:repo.name/issues/comments")

(defapiget-ghubp "/repos/:owner/:repo/issues/comments/:id"
  "Get a single comment."
  "issues/comments/#get-a-single-comment"
  (repo thread) "/repos/:repo.owner.login/:repo.name/issues/comments/:thread.id")

(defapipatch-ghubp "/repos/:owner/:repo/issues/:number/comments"
  "Create a comment."
  "issues/comments/#create-a-comment"
  (repo issue) "/repos/:repo.owner.login/:repo.name/issues/:issue.number/comments")

(defapipatch-ghubp "/repos/:owner/:repo/issues/comments/:id"
  "Edit a comment."
  "issues/comments/#edit-a-comment"
  (repo thread) "/repos/:repo.owner.login/:repo.name/issues/comments/:thread.id")

(defapidelete-ghubp "/repos/:owner/:repo/issues/comments/:id"
  "Delete a comment."
  "issues/comments/#delete-a-comment"
  (repo thread) "/repos/:repo.owner.login/:repo.name/issues/comments/:thread.id")


;;; Issue Events:

(defapiget-ghubp "/repos/:owner/:repo/issues/:number/events"
  ;; note: :number changed from :issue_number for consistency
  "List events for an issue."
  "issues/events/#list-events-for-an-issue"
  (repo issue) "/repos/:repo.owner.login/:repo.name/issues/:issue.number/events")

(defapiget-ghubp "/repos/:owner/:repo/issues/events"
  "List events for a repository."
  "issues/events/#list-events-for-a-repository"
  (repo) "/repos/:repo.owner.login/:repo.name/issues/events")

(defapiget-ghubp "/repos/:owner/:repo/issues/events/:id"
  "Get a single event."
  "issues/events/#get-a-single-event"
  (repo thread) "/repos/:repo.owner.login/:repo.name/issues/events/:thread.id")


;;; Issue Labels:

(defapiget-ghubp "/repos/:owner/:repo/labels"
  "List all labels for this repository."
  "issues/labels/#list-all-labels-for-this-repository"
  (repo) "/repos/:repo.owner.login/:repo.name/labels")

(defapiget-ghubp "/repos/:owner/:repo/labels/:name"
  "Get a single label."
  "issues/labels/#get-a-single-label"
  (repo label) "/repos/:repo.owner.login/:repo.name/labels/:label.name")

(defapipost-ghubp "/repos/:owner/:repo/labels"
  "Create a label."
  "issues/labels/#create-a-label"
  (repo) "/repos/:repo.owner.login/:repo.name/labels")

(defapipatch-ghubp "/repos/:owner/:repo/labels/:name"
  "Update a label."
  "issues/labels/#update-a-label"
  (repo label) "/repos/:repo.owner.login/:repo.name/labels/:label.name")

(defapidelete-ghubp "/repos/:owner/:repo/labels/:name"
  "Delete a label."
  "issues/labels/#deleted-a-label"
  (repo label) "/repos/:repo.owner.login/:repo.name/labels/:label.name")

(defapiget-ghubp "/repos/:owner/:repo/issues/:number/labels"
  "List labels on an issue."
  "issues/labels/#list-labels-on-an-issue"
  (repo issue) "/repos/:repo.owner.login/:repo.name/issues/:issue.number/labels")

(defapipost-ghubp "/repos/:owner/:repo/issues/:number/labels"
  "Add labels to an issue."
  "issues/labels/#add-labels-to-an-issue"
  (repo issue) "/repos/:repo.owner.login/:repo.name/issues/:issue.number/labels"
  :pre-process-data (apply-partially #'ghubp-get-in-all '(name)))

(defapidelete-ghubp "/repos/:owner/:repo/issues/:number/labels/:name"
  "Remove a label from an issue."
  "issues/labels/#remove-a-label-from-an-issue"
  (repo issue label) "/repos/:repo.owner.login/:repo.name/issues/:issue.number/labels/:label.name")

(defapipatch-ghubp "/repos/:owner/:repo/issues/:number/labels"
  "Replace all labels for an issue."
  "issues/labels/#replace-all-labels-for-an-issue"
  (repo issue) "/repos/:repo.owner.login/:repo.name/issues/:issue.number/labels"
  :pre-process-data (apply-partially #'ghubp-get-in-all '(name)))

(defapidelete-ghubp "/repos/:owner/:repo/issues/:number/labels"
  "Remove all labels from an issue."
  "issues/labels/#remove-all-labels-from-an-issue"
  (repo issue) "/repos/:repo.owner.login/:repo.name/issues/:issue.number/labels")

(defapiget-ghubp "/repos/:owner/:repo/milestones/:number/labels"
  "Get labels for every issue in a milestone."
  "issues/labels/#get-labels-for-every-issue-in-a-milestone"
  (repo milestone) "/repos/:repo.owner.login/:repo.name/milestones/:milestone.number/labels")


;;; Issue Milestones:

(defapiget-ghubp "/repos/:owner/:repo/milestones"
  "List milestones for a repository."
  "issues/milestones/#list-milestones-for-a-repository"
  (repo) "/repos/:repo.owner.login/:repo.name/milestones")

(defapiget-ghubp "/repos/:owner/:repo/milestones/:number"
  "Get a single milestone."
  "issues/milestones/#get-a-single-milestone"
  (repo milestone) "/repos/:repo.owner.login/:repo.name/milestones/:milestone.number")

(defapipost-ghubp "/repos/:owner/:repo/milestones"
  "Create a milestone."
  "issues/milestones/#create-a-milestone"
  (repo) "/repos/:repo.owner.login/:repo.name/milestones")

(defapipatch-ghubp "/repos/:owner/:repo/milestones/:number"
  "Update a milestone."
  "issues/milestones/#create-a-milestone"
  (repo milestone) "/repos/:repo.owner.login/:repo.name/milestones/:milestone.number")

(defapidelete-ghubp "/repos/:owner/:repo/milestones/:number"
  "Delete a milestone."
  "issues/milestones/#delete-a-milestone"
  (repo milestone) "/repos/:repo.owner.login/:repo.name/milestones/:milestone.number")


;;; Organizations:

(defapiget-ghubp "/user/orgs"
  "List organizations for the authenticated user."
  "orgs/#list-your-organizations")

(defapiget-ghubp "/organizations"
  "Lists all organizations in the order that they were created on GitHub."
  "orgs/#list-all-organizations")

(defapiget-ghubp "/users/:username/orgs"
  "List public organization memberships for the specified user."
  "orgs/#list-user-organizations"
  (user) "/users/:user.login/orgs")

(defapiget-ghubp "/orgs/:org"
  "Get an organization."
  "orgs/#get-an-organization"
  (org) "/orgs/:org.login")

(defapipatch-ghubp "/orgs/:org"
  "Edit an organization."
  "orgs/#edit-an-organization"
  (org) "/orgs/:org.login")


;;; Pull Request:

(defapiget-ghubp "/repos/:owner/:repo/pulls"
  "List pull requests."
  "pulls/#list-pull-requests"
  (repo) "/repos/:repo.owner.login/:repo.name/pulls")

(defapiget-ghubp "/repos/:owner/:repo/pulls/:number"
  "Get a single pull request."
  "pulls/#get-a-single-pull-request"
  (repo pull-request) "/repos/:repo.owner.login/:repo.name/pulls/:pull-request.number")

(defapipost-ghubp "/repos/:owner/:repo/pulls"
  "Create a pull request."
  "pulls/#create-a-pull-request"
  (repo) "/repos/:repo.owner.login/:repo.name/pulls")

(defapipatch-ghubp "/repos/:owner/:repo/pulls/:number"
  "Update a pull request."
  "pulls/#update-a-pull-request"
  (repo pull-request) "/repos/:repo.owner.login/:repo.name/pulls/:pull-request.number")

(defapiget-ghubp "/repos/:owner/:repo/pulls/:number/commits"
  "List commits on a pull request."
  "pulls/#list-commits-on-a-pull-request"
  (repo pull-request) "/repos/:repo.owner.login/:repo.name/pulls/:pull-request.number/commits")

(defapiget-ghubp "/repos/:owner/:repo/pulls/:number/files"
  "List pull request files."
  "pulls/#list-pull-requests-files"
  (repo pull-request) "/repos/:repo.owner.login/:repo.name/pulls/:pull-request.number/files")

(defapiget-ghubp "/repos/:owner/:repo/pulls/:number/merge"
  "Get if a pull request has been merged."
  "pulls/#get-if-a-pull-request-has-been-merged"
  (repo pull-request) "/repos/:repo.owner.login/:repo.name/pulls/:pull-request.number/merge")

(defapiput-ghubp "/repos/:owner/:repo/pulls/:number/merge"
  "Merge a pull request (Merge Button)"
  "pulls/#merge-a-pull-request-merge-button"
  (repo pull-request) "/repos/:repo.owner.login/:repo.name/pulls/:pull-request.number/merge")


;;; Pull Request Reviews:

(defapiget-ghubp "/repos/:owner/:repo/pulls/:number/reviews"
  "List reviews on a pull request."
  "pulls/reviews/#list-reviews-on-a-pull-request"
  (repo pull-request) "/repos/:repo.owner.login/:repo.name/pulls/:pull-request.number/reviews")

(defapiget-ghubp "/repos/:owner/:repo/pulls/:number/reviews/:id"
  "Get a single review."
  "pulls/reviews/#list-reviews-on-a-pull-request"
  (repo pull-request review) "/repos/:repo.owner.login/:repo.name/pulls/:pull-request.number/reviews/:review.id")

(defapidelete-ghubp "/repos/:owner/:repo/pulls/:number/reviews/:id"
  "Delete a pending review."
  "pulls/reviews/#delete-a-pending-review"
  (repo pull-request review) "/repos/:repo.owner.login/:repo.name/pulls/:pull-request.number/reviews/:review.id")

(defapiget-ghubp "/repos/:owner/:repo/pulls/:number/reviews/:id/comments"
  "Get comments for a single review."
  "pulls/reviews/#get-comments-for-a-single-review"
  (repo pull-request review) "/repos/:repo.owner.login/:repo.name/pulls/:pull-request.number/reviews/:review.id/comments")

(defapipost-ghubp "/repos/:owner/:repo/pulls/:number/reviews"
  "Create a pull request review."
  "pulls/reviews/#create-a-pull-request-review"
  (repo pull-request) "/repos/:repo.owner.login/:repo.name/pulls/:pull-request.number/reviews")

(defapipost-ghubp "/repos/:owner/:repo/pulls/:number/reviews/:id/events"
  "Submit a pull request review."
  "pulls/reviews/#submit-a-pull-request-review"
  (repo pull-request review) "/repos/:repo.owner.login/:repo.name/pulls/:pull-request.number/reviews/:review.id/events")

(defapiput-ghubp "/repos/:owner/:repo/pulls/:number/reviews/:id/dismissals"
  "Dismiss a pull request review."
  "pulls/reviews/#dismiss-a-pull-request-review"
  (repo pull-request review) "/repos/:repo.owner.login/:repo.name/pulls/:pull-request.number/reviews/:review.id/dismissals")


;;; Pull Request Review Comments:

(defapiget-ghubp "/repos/:owner/:repo/pulls/:number/comments"
  "List comments on a pull request."
  "pulls/comments/#list-comments-on-a-pull-request"
  (repo pull-request) "/repos/:repo.owner.login/:repo.name/pulls/:pull-request.number/comments")

(defapiget-ghubp "/repos/:owner/:repo/pulls/comments"
  "List comments in a repository."
  "pulls/comments/#list-comments-in-a-repository"
  (repo) "/repos/:repo.owner.login/:repo.name/pulls/comments")

(defapiget-ghubp "/repos/:owner/:repo/pulls/comments/:id"
  "Get a single comment."
  "pulls/comments/#get-a-single-comment"
  (repo thread) "/repos/:repo.owner.login/:repo.name/pulls/comments/:thread.id")

(defapipost-ghubp "/repos/:owner/:repo/pulls/:number/comments"
  "Create a comment."
  "pulls/comments/#create-a-comment"
  (repo pull-request) "/repos/:repo.owner.login/:repo.name/pulls/:pull-request.number/comments")

(defapipatch-ghubp "/repos/:owner/:repo/pulls/comments/:id"
  "Edit a comment."
  "pulls/comments/#edit-a-comment"
  (repo thread) "/repos/:repo.owner.login/:repo.name/pulls/comments/:thread.id")

(defapidelete-ghubp "/repos/:owner/:repo/pulls/comments/:id"
  "Delete a comment."
  "pulls/comments/#delete-a-comment"
  (repo thread) "/repos/:repo.owner.login/:repo.name/pulls/comments/:thread.id")


;;; Pull Request Review Requests:

(defapiget-ghubp "/repos/:owner/:repo/pulls/:number/requested_reviewers"
  "List review requests."
  "pulls/review_requests/#list-review-requests"
  (repo pull-request) "/repos/:repo.owner.login/:repo.name/pulls/:pull-request.number/requested_reviewers")

(defapipost-ghubp "/repos/:owner/:repo/pulls/:number/requested_reviewers"
  "Create a review request."
  "pulls/review_requests/#create-a-review-request"
  (repo pull-request) "/repos/:repo.owner.login/:repo.name/pulls/:pull-request.number/requested_reviewers")

(defapidelete-ghubp "/repos/:owner/:repo/pulls/:number/requested_reviewers"
  "Delete a review request."
  "pulls/review_requests/#delete-a-review-request"
  (repo pull-request) "/repos/:repo.owner.login/:repo.name/pulls/:pull-request.number/requested_reviewers")


;;; Reactions:

(defapiget-ghubp "/repos/:owner/:repo/comments/:id/reactions"
  "List reactions for a commit comment."
  "reactions/#list-reactions-for-a-commit-comment"
  (repo thread) "/repos/:repo.owner.login/:repo.name/comments/:thread.id/reactions")

(defapipost-ghubp "/repos/:owner/:repo/comments/:id/reactions"
  "Create reaction for a commit comment."
  "reactions/#create-reaction-for-a-commit-comment"
  (repo thread) "/repos/:repo.owner.login/:repo.name/comments/:thread.id/reactions")

(defapiget-ghubp "/repos/:owner/:repo/issues/:number/reactions"
  "List reactions for an issue."
  "reactions/#list-reactions-for-an-issue"
  (repo issue) "/repos/:repo.owner.login/:repo.name/issues/:issue.number/reactions")

(defapipost-ghubp "/repos/:owner/:repo/issues/:number/reactions"
  "Create reaction for an issue."
  "reactions/#create-reaction-for-an-issue"
  (repo issue) "/repos/:repo.owner.login/:repo.name/issues/:issue.number/reactions")

(defapiget-ghubp "/repos/:owner/:repo/issues/comments/:id/reactions"
  "List reactions for an issue comment."
  "reactions/#list-reactions-for-an-issue-comment"
  (repo thread) "/repos/:repo.owner.login/:repo.name/issues/comments/:thread.id/reactions")

(defapipost-ghubp "/repos/:owner/:repo/issues/comments/:id/reactions"
  "Create reaction for an issue comment."
  "reactions/#create-reaction-for-an-issue-comment"
  (repo thread) "/repos/:repo.owner.login/:repo.name/issues/comments/:thread.id/reactions")

(defapiget-ghubp "/repos/:owner/:repo/pulls/comments/:id/reactions"
  "List reactions for a pull request review comment."
  "reactions/#list-reactions-for-a-pull-request-review-comment"
  (repo thread) "/repos/:repo.owner.login/:repo.name/pulls/comments/:thread.id/reactions")

(defapipost-ghubp "/repos/:owner/:repo/pulls/comments/:id/reactions"
  "Create reaction for a pull request review comment."
  "reactions/#create-reaction-for-a-pull-request-review-comment"
  (repo thread) "/repos/:repo.owner.login/:repo.name/pulls/comments/:thread.id/reactions")

(defapidelete-ghubp "/reactions/:id"
  "Delete a reaction."
  "reactions/#delete-a-reaction"
  (thread) "/reactions/:thread.id")


;;; Repositories:

(defapiget-ghubp "/user/repos"
  "List your repositories.
List repositories that are accessible to the authenticated user.

This includes repositories owned by the authenticated user,
repositories where the authenticated user is a collaborator, and
repositories that the authenticated user has access to through an
organization membership."
  "repos/#list-your-repositories")

(defapiget-ghubp "/users/:username/repos"
  "List user repositories.
List public repositories for the specified user."
  "repos/#list-user-repositories"
  (user) "/users/:user.login/repos")

(defapiget-ghubp "/orgs/:org/repos"
  "List organization repositories.
List repositories for the specified org."
  "repos/#list-organization-repositories"
  (org) "/orgs/:org.login/repos")

(defapiget-ghubp "/repositories"
  "List all public repositories.
This provides a dump of every public repository, in the order
that they were created."
  "repos/#list-all-public-repositories")

(defapipost-ghubp "/user/repos"
  "Create.
Create a new repository for the authenticated user.  (Currently
not enabled for Integrations)."
  "repos/#create")

(defapipost-ghubp "/orgs/:org/repos"
  "Create a new repository in this organization.
The authenticated user must be a member of the specified
organization."
  "repos/#create"
  (org) "/orgs/:org.login/repos")

(defapiget-ghubp "/repos/:owner/:repo"
  "Get a specific repository object."
  "repos/#get"
  (repo) "/repos/:repo.owner.login/:repo.name"
  :condition-case
  ((ghub-404 nil)))


;;; Users:
(defapiget-ghubp "/users/:username"
  "Get a single user."
  "users/#get-a-single-user"
  (user) "/users/:user.login")

(defapiget-ghubp "/user"
  "Get the authenticated user."
  "users/#get-the-authenticated-user")

(defapipatch-ghubp "/user"
  "Update the authenticated user."
  "users/#update-the-authenticated-user")

(defapiget-ghubp "/users"
  "Get all users.
Lists all users, in the order that they signed up on GitHub. This
list includes personal user accounts and organization accounts."
  "users/#get-all-users")

;; Users - Emails

(defapiget-ghubp "/user/emails"
  "List email addresses for a user."
  "users/emails/#list-email-addresses-for-a-user")

(defapiget-ghubp "/user/public_emails"
  "List public email addresses for a user."
  "users/emails/#list-public-email-addresses-for-a-user")

(defapipost-ghubp "/user/emails"
  "Add email address(es).
You can post a single email address or an array of addresses."
  "users/emails/#add-email-addresses")

(defapidelete-ghubp "/user/emails"
  "Delete email address(es).
You can post a single email address or an array of addresses."
  "users/emails/#add-email-addresses")

(defapipatch-ghubp "/user/email/visibility"
  "Toggle primary email visibility."
  "users/emails/#toggle-primary-email-visibility")

;; Users - Followers

(defapiget-ghubp "/users/:username/followers"
  "List a user's followers."
  "users/followers/#list-followers-of-a-user"
  (user) "/users/:user.login/followers")

(defapiget-ghubp "/user/followers"
  "List the authenticated user's followers."
  "users/followers/#list-followers-of-a-user")

(defapiget-ghubp "/users/:username/following"
  "List who USER is following."
  "users/followers/#list-users-followed-by-another-user"
  (user) "/users/:user.login/following")

(defapiget-ghubp "/user/following"
  "List who the authenticated user is following."
  "users/followers/#list-users-followed-by-another-user")

(defapiget-ghubp "/user/following/:username"
  "Check if you are following USER."
  "users/followers/#check-if-you-are-following-a-user"
  (user) "/user/following/:user.login")

(defapiget-ghubp "/users/:username/following/:target_user"
  "Check if USER-1 follows USER-2."
  "users/followers/#check-if-you-are-following-a-user"
  (user-1 user-2) "/users/:user-1.login/following/:user-2.login")

(defapiput-ghubp "/user/following/:username"
  "Follow USER."
  "users/followers/#follow-a-user"
  (user) "/user/following/:user.login")

(defapidelete-ghubp "/user/following/:username"
  "Unfollow USER."
  "users/followers/#unfollow-a-user"
  (user) "/user/following/:user.login")

;; Users - Git SSH Keys

(defapiget-ghubp "/users/:username/keys"
  "Lists the verified public keys for a user.
This is accessible by anyone."
  "users/keys/#list-public-keys-for-a-user"
  (user) "/users/:user.login/keys")

(defapiget-ghubp "/user/keys"
  "List your public keys."
  "users/keys/#list-your-public-keys")

(defapiget-ghubp "/user/keys/:id"
  "Get a single public key."
  "users/keys/#get-a-single-public-key"
  (key) "/user/keys/:key.id")

(defapiput-ghubp "/user/keys"
  "Create a public key."
  "users/keys/#create-a-public-key")

(defapidelete-ghubp "/user/keys/:id"
  "Delete a single public key."
  "users/keys/#get-a-single-public-key"
  (key) "/user/keys/:key.id")

;; Users - GPG Keys

;; TODO: Currently in preview.

;; https://developer.github.com/v3/users/gpg_keys/

;; Users - Blocking

;; TODO: Currently in preview.

;; https://developer.github.com/v3/users/blocking/

;; Activity - Notifications

;; TODO: It would be nice if ghub+ could offer 'smart' polling for
;; notifications to trim down on API requests.  This smart polling is
;; supported by GitHub for notifications in particular.  If done
;; right, we could offer a 'push'-type interface to handle when new
;; notifications are received.

;; (ghubp-notifications-{start,stop}-polling)
;; ghubp-notifications-received-hook

(defapiget-ghubp "/notifications"
  "Get the user's notifications."
  "activity/notifications/#list-your-notifications")

(defapiget-ghubp
  "/repos/:owner/:repo/notifications"
  "List your notifications in a repository."
  "activity/notifications/#list-your-notifications-in-a-repository"
  (user repo) "/repos/:user.login/:repo.name/notifications")

(defapiput-ghubp "/notifications"
  "Mark as read.
Marking a notification as \"read\" removes it from the default
view on GitHub."
  "activity/notifications/#mark-as-read")

(defapiput-ghubp "/repos/:owner/:repo/notifications"
  "Mark notifications as read in a repository.
Marking all notifications in a repository as \"read\" removes
them from the default view on GitHub."
  "activity/notifications/#mark-notifications-as-read-in-a-repository"
  (user repo) "/repos/:user.login/:repo.name/notifications")

(defapiget-ghubp "/notifications/threads/:id"
  "View a single thread."
  "activity/notifications/#view-a-single-thread"
  (thread) "/notifications/threads/:thread.id")

(defapipatch-ghubp "/notifications/threads/:id"
  "Mark a thread as read."
  "activity/notifications/#mark-a-thread-as-read"
  (thread) "/notifications/threads/:thread.id")

(defapiget-ghubp "/notifications/threads/:id/subscription"
  "Get a thread subscription.
This checks to see if the current user is subscribed to a
thread."
  "activity/notifications/#get-a-thread-subscription"
  (thread) "/notifications/threads/:thread.id/subscription")

(defapiput-ghubp "/notifications/threads/:id/subscription"
  "Set a thread subscription.
This lets you subscribe or unsubscribe from a conversation.
Unsubscribing from a conversation mutes all future
notifications (until you comment or get @mentioned once more)."
  "activity/notifications/#set-a-thread-subscription"
  (thread) "/notifications/threads/:thread.id/subscription")

(defapidelete-ghubp "/notifications/threads/:id/subscription"
  "Delete a thread subscription."
  "activity/notifications/#delete-a-thread-subscription"
  (thread) "/notifications/threads/:thread.id/subscription")


;;; Unfiled:

(defapiget-ghubp "/repos/:owner/:repo/commits/:ref/statuses"
  "List statuses for a specific ref"
  "repos/statuses/#list-statuses-for-a-specific-ref"
  (repo ref) "/repos/:repo.owner.login/:repo.name/commits/:ref/statuses")

(defapiget-ghubp "/repos/:owner/:repo/commits/:ref/status"
  "Get the combined status for a specific ref"
  "repos/statuses/#get-the-combined-status-for-a-specific-ref"
  (repo ref) "/repos/:repo.owner.login/:repo.name/commits/:ref/status")

(defapipost-ghubp "/repos/:owner/:repo/forks"
  "Create a fork for the authenticated user."
  "repos/forks/#create-a-fork"
  (repo) "/repos/:repo.owner.login/:repo.name/forks")

(defapipost-ghubp "/repos/:owner/:repo/issues/:number/comments"
  "Post a comment to an issue"
  "issues/comments/#create-a-comment"
  (repo issue) "/repos/:repo.owner.login/:repo.name/issues/:issue.number/comments")

(defapiget-ghubp "/repos/:owner/:repo/commits"
  "List commits on a repository"
  "repos/commits/#list-commits-on-a-repository"
  (repo) "/repos/:repo.owner.login/:repo.name/commits")

(defun ghubp-url-parse (url)
  "Parse URL for its type and API callback.

A cons cell is returned.  The car is one of

 - `issue'
 - `pull-request'

and the cdr is a callback suitable for `ghub-get', etc."
  (let ((callback (url-filename (url-generic-parse-url url))))
    (cons
     (cond
      ((string-match-p (rx bol "/repos/" (+? any) "/" (+? any) "/issues/" (+ digit) eol)
                       callback)
       'issue)
      ((string-match-p (rx bol "/repos/" (+? any) "/" (+? any) "/pulls/" (+ digit) eol)
                       callback)
       'pull-request)
      (t 'unknown))
     callback)))

(provide 'ghub+)
;;; ghub+.el ends here
