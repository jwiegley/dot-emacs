;;; magithub-issue.el --- Browse issues with Magithub  -*- lexical-binding: t; -*-

;; Copyright (C) 2016-2017  Sean Allred

;; Author: Sean Allred <code@seanallred.com>
;; Keywords: tools

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

;; Jump to issues from `magit-status'!

;;; Code:

(require 's)
(require 'dash)
(require 'ghub+)
(require 'cl-lib)
(require 'magit)

(require 'magithub-core)
(require 'magithub-user)
(require 'magithub-label)

(declare-function magithub-issue-view "magithub-issue-view.el" (issue))

(defvar-local magithub-issue nil
  "The issue object associated with a buffer.")

(defvar magit-magithub-repo-issues-section-map
  (let ((m (make-sparse-keymap)))
    (define-key m [remap magit-visit-thing] #'magithub-repo-visit-issues)
    m))

(defvar magit-magithub-note-section-map
  (let ((m (make-sparse-keymap)))
    (set-keymap-parent m magithub-map)
    (define-key m [remap magit-visit-thing] #'magithub-issue-personal-note)
    m))

;; Core
(defmacro magithub-interactive-issue-or-pr (sym args doc &rest body)
  "Declare an interactive form that works on both issues and PRs.
SYM is a postfix for the function symbol.  An appropriate prefix
will be added for both the issue-version and PR-version.

ARGS should be a list of one element, the symbol ISSUE-OR-PR.

DOC is a doc-string.

BODY is the function implementation."
  (declare (indent defun)
           (doc-string 3))
  (unless (eq (car args) 'issue-or-pr)
    (error "For clarity, the first argument must be ISSUE-OR-PR"))
  (let* ((snam (symbol-name sym))
         (isym (intern (concat "magithub-issue-" snam)))
         (psym (intern (concat "magithub-pull-request-" snam))))
    `(list
      (defun ,isym ,(cons 'issue (cdr args))
        ,(format (concat doc "\n\nSee also `%S'.") "ISSUE" psym)
        (interactive (list (magithub-interactive-issue)))
        (let ((issue-or-pr issue))
          ,@body))
      (defun ,psym ,(cons 'pull-request (cdr args))
        ,(format (concat doc "\n\nSee also `%S'.") "PULL-REQUEST" isym)
        (interactive (list (magithub-interactive-pull-request)))
        (let ((issue-or-pr pull-request))
          ,@body)))))

(defun magithub--issue-list (&rest params)
  "Return a list of issues for the current repository.
The response is unpaginated, so avoid doing this with PARAMS that
will return a ton of issues.

See also `ghubp-get-repos-owner-repo-issues'."
  (cl-assert (cl-evenp (length params)))
  (magithub-cache :issues
    `(ghubp-unpaginate
      (ghubp-get-repos-owner-repo-issues
       ',(magithub-repo)
       ,@params))
    :message
    "Retrieving issue list..."))

(defun magithub-issue--issue-is-pull-p (issue)
  (not (null (alist-get 'pull_request issue))))

(defun magithub-issue--issue-is-issue-p (issue)
  (and (alist-get 'number issue)
       (not (magithub-issue--issue-is-pull-p issue))))

(defun magithub-issue-comments (issue)
  "Get comments on ISSUE."
  (let ((repo (magithub-issue-repo issue)))
    (magithub-cache :issues
      `(ghubp-get-repos-owner-repo-issues-number-comments ',repo ',issue))))

;; Finding issues and pull requests
(defun magithub-issues ()
  "Return a list of issue objects that are actually issues."
  (-filter #'magithub-issue--issue-is-issue-p
           (magithub--issue-list)))

(defun magithub-pull-requests ()
  "Return a list of issue objects that are actually pull requests."
  (-filter #'magithub-issue--issue-is-pull-p
           (magithub--issue-list)))

;; Sorting
(defcustom magithub-issue-sort-function
  #'magithub-issue-sort-ascending
  "Function used for sorting issues and pull requests in the
status buffer.  Should take two issue-objects as arguments."
  :type 'function
  :group 'magithub)

(magithub-defsort magithub-issue-sort-ascending #'<
  "Lower issue numbers come first."
  (apply-partially #'alist-get :number))

(magithub-defsort magithub-issue-sort-descending #'>
  "Higher issue numbers come first."
  (apply-partially #'alist-get :number))

(defun magithub-issue--sort (issues)
  "Sort ISSUES by `magithub-issue-sort-function'."
  (sort issues magithub-issue-sort-function))

;; Getting issues from the user
(defun magithub-issue--format-for-read (issue)
  "Format ISSUE as a string suitable for completion."
  (let-alist issue (format "%3d %s" .number .title)))

(defun magithub-issue--completing-read (prompt default preds)
  "Complete over all open pull requests returning its issue object.
If point is on a pull-request object, that object is selected by
default."
  (magithub--completing-read prompt (magithub--issue-list)
                             #'magithub-issue--format-for-read
                             (apply-partially #'magithub--satisfies-p preds)
                             t default))
(defun magithub-issue-completing-read-issues (&optional default)
  "Read an issue in the minibuffer with completion."
  (interactive (list (magithub-thing-at-point 'issue)))
  (magithub-issue--completing-read
   "Issue: " default (list #'magithub-issue--issue-is-issue-p)))
(defun magithub-issue-completing-read-pull-requests (&optional default)
  "Read a pull request in the minibuffer with completion."
  (interactive (list (magithub-thing-at-point 'pull-request)))
  (magithub-issue--completing-read
   "Pull Request: " default (list #'magithub-issue--issue-is-pull-p)))
(defun magithub-interactive-issue ()
  (or (magithub-thing-at-point 'issue)
      (magithub-issue-completing-read-issues)))
(defun magithub-interactive-pull-request ()
  (or (magithub-thing-at-point 'pull-request)
      (magithub-issue-completing-read-pull-requests)))

(defun magithub-issue-find (number)
  "Return the issue or pull request with the given NUMBER."
  (-find (lambda (i) (= (alist-get 'number i) number))
         (magithub--issue-list :filter "all" :state "all")))

(defun magithub-issue (repo number)
  "Retrieve in REPO issue NUMBER."
  (magithub-cache :issues
    `(ghubp-get-repos-owner-repo-issues-number
      ',repo '((number . ,number)))
    :message
    (format "Getting issue %s#%d..." (magithub-repo-name repo) number)))

(defun magithub-issue-personal-note-file (issue-or-pr)
  "Return an absolute filename appropriate for ISSUE-OR-PR."
  (let-alist `((repo . ,(magithub-repo (magithub-issue-repo issue-or-pr)))
               (issue . ,issue-or-pr))
    (expand-file-name
     (format "%s/%s/notes/%d.org" .repo.owner.login .repo.name .issue.number)
     magithub-dir)))

(magithub-interactive-issue-or-pr personal-note (issue-or-pr)
  "Write a personal note about %s.
This is stored in `magit-git-dir' and is unrelated to
`git-notes'."
  (if (null issue-or-pr)
      (error "No issue or pull request here")
    (let-alist issue-or-pr
      (let ((note-file (magithub-issue-personal-note-file issue-or-pr)))
        (make-directory (file-name-directory note-file) t)
        (with-current-buffer (find-file-other-window note-file)
          (rename-buffer (format "*magithub note for #%d*" .number)))))))

(defun magithub-issue-has-personal-note-p (issue-or-pr)
  "Non-nil if a personal note exists for ISSUE-OR-PR."
  (let ((filename (magithub-issue-personal-note-file issue-or-pr)))
    (and (file-exists-p filename)
         (not (string-equal
               ""
               (string-trim
                (with-temp-buffer
                  (insert-file-contents-literally filename)
                  (buffer-string))))))))

(defun magithub-issue-repo (issue)
  "Get a repository object from ISSUE."
  (let-alist issue
    (save-match-data
      (when (string-match (concat (rx bos)
                                  (regexp-quote ghub-base-url)
                                  (rx "/repos/"
                                      (group (+ (not (any "/")))) "/"
                                      (group (+ (not (any "/")))) "/issues/")
                                  (regexp-quote (number-to-string .number))
                                  (rx eos))
                          .url)
        (magithub-repo
         `((owner (login . ,(match-string 1 .url)))
           (name . ,(match-string 2 .url))))))))

(defun magithub-issue-reference (issue)
  "Return a string like \"owner/repo#number\" for ISSUE."
  (let-alist `((repo . ,(magithub-issue-repo issue))
               (issue . ,issue))
    (format "%s/%s#%d" .repo.owner.login .repo.name .issue.number)))

(defun magithub-issue-from-reference (string)
  "Parse an issue from an \"owner/repo#number\" STRING."
  (when (string-match (rx bos (group (+ any))
                          "/" (group (+ any))
                          "#" (group (+ digit))
                          eos)
                      string)
    (magithub-issue `((owner (login . ,(match-string 1 string)))
                      (name . ,(match-string 2 string)))
                    (string-to-number (match-string 3 string)))))

(defun magithub-issue-insert-sections (issues)
  "Insert ISSUES into the buffer with alignment.
See also `magithub-issue-insert-section'."
  (let ((max-num-len (thread-last issues
                       (ghubp-get-in-all '(number))
                       (apply #'max)
                       (number-to-string)
                       (length))))
    (--map (magithub-issue-insert-section it max-num-len)
           issues)))

(defun magithub-issue-insert-section (issue &optional pad-num-to-len)
  "Insert ISSUE into the buffer.
If PAD-NUM-TO-LEN is non-nil, it is an integer width.  For
example, if this section's issue number is \"3\" and the next
section's number is \"401\", pass a padding of 3 to both to align
them.

See also `magithub-issue-insert-sections'."
  (when issue
    (setq pad-num-to-len (or pad-num-to-len 0))
    (magit-insert-section (magithub-issue issue t)
      (let-alist issue
        (magit-insert-heading
          (format (format "%%%ds  %%s" (1+ pad-num-to-len)) ;1+ accounts for #
                  (propertize (format "#%d" .number) 'face 'magithub-issue-number)
                  (propertize .title                 'face (if (magithub-issue-has-personal-note-p issue)
                                                               'magithub-issue-title-with-note
                                                             'magithub-issue-title))))
        (run-hook-with-args 'magithub-issue-details-hook issue
                            (format " %s  %%-12s" (make-string pad-num-to-len ?\ )))))))

(defvar magithub-issue-details-hook
  '(magithub-issue-detail-insert-personal-notes
    magithub-issue-detail-insert-created
    magithub-issue-detail-insert-updated
    magithub-issue-detail-insert-author
    magithub-issue-detail-insert-assignees
    magithub-issue-detail-insert-labels
    magithub-issue-detail-insert-body-preview)
  "Detail functions for issue-type sections.
These details appear under issues as expandable content.

Each function takes two arguments:

 1. an issue object
 2. a format string for a string label (for alignment)")

(defun magithub-issue-detail-insert-author (issue fmt)
  "Insert the author of ISSUE using FMT."
  (let-alist issue
    (insert (format fmt "Author:"))
    (magit-insert-section (magithub-user (magithub-user .user))
      (insert
       (propertize .user.login 'face 'magithub-user)))
    (insert "\n")))

(defun magithub-issue-detail-insert-created (issue fmt)
  "Insert when ISSUE was created using FMT."
  (let-alist issue
    (insert (format fmt "Created:")
            (propertize .created_at 'face 'magit-dimmed)
            "\n")))

(defun magithub-issue-detail-insert-updated (issue fmt)
  "Insert when ISSUE was created using FMT."
  (let-alist issue
    (insert (format fmt "Updated:")
            (propertize .updated_at 'face 'magit-dimmed)
            "\n")))

(defun magithub-issue-detail-insert-assignees (issue fmt)
  "Insert the assignees of ISSUE using FMT."
  (let-alist issue
    (insert (format fmt "Assignees:"))
    (if .assignees
        (let ((assignees .assignees) assignee)
          (while (setq assignee (pop assignees))
            (magit-insert-section (magithub-assignee (magithub-user assignee))
              (insert (propertize (alist-get 'login assignee)
                                  'face 'magithub-user)))
            (when assignees
              (insert " "))))
      (magit-insert-section (magithub-assignee)
        (insert (propertize "none" 'face 'magit-dimmed))))
    (insert "\n")))

(defun magithub-issue-detail-insert-personal-notes (issue fmt)
  "Insert a link to ISSUE's notes."
  (insert (format fmt "My notes:"))
  (magit-insert-section (magithub-note)
    (insert (if (magithub-issue-has-personal-note-p issue)
                (propertize "visit your note" 'face 'link)
              (propertize "create a new note" 'face 'magit-dimmed))))
  (insert "\n"))

(defun magithub-issue-detail-insert-body-preview (issue fmt)
  "Insert a preview of ISSUE's body using FMT."
  (let-alist issue
    (let (label-string label-len width did-cut maxchar text)
      (setq label-string (format fmt "Preview:"))
      (insert label-string)

      (if (or (null .body) (string= .body ""))
          (concat (propertize "none" 'face 'magit-dimmed))

        (setq label-len (length label-string))
        (setq width (- fill-column label-len))
        (setq maxchar (* 3 width))
        (setq did-cut (< maxchar (length .body)))
        (setq maxchar (if did-cut (- maxchar 3) maxchar))
        (setq text (if did-cut (substring .body 0 (min (length .body) (* 4 width))) .body))
        (setq text (replace-regexp-in-string "" "" text))
        (setq text (let ((fill-column width))
                     (thread-last text
                       (magithub-fill-gfm)
                       (magithub-indent-text label-len)
                       (s-trim))))
        (insert text)
        (when did-cut
          (insert (propertize "..." 'face 'magit-dimmed)))
        (insert "\n")))))

(defun magithub-issue-detail-insert-labels (issue fmt)
  "Insert ISSUE's labels using FMT."
  (let-alist issue
    (insert (format fmt "Labels:"))
    (magithub-label-insert-list .labels)
    (insert "\n")))

;; Magithub-Status stuff

(defun magithub-issue-refresh (even-if-offline)
  "Refresh issues for this repository.
If EVEN-IF-OFFLINE is non-nil, we'll still refresh (that is,
we'll hit the API) if Magithub is offline."
  (interactive "P")
  (let ((magithub-cache (if even-if-offline nil magithub-cache)))
    (magithub-cache-without-cache :issues
      (ignore (magithub--issue-list))))
  (when (derived-mode-p 'magit-status-mode)
    (magit-refresh)))

(defvar magit-magithub-issue-section-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map magithub-map)
    (define-key map [remap magit-visit-thing] #'magithub-issue-visit)
    (define-key map [remap magithub-browse-thing] #'magithub-issue-browse)
    (define-key map [remap magithub-reply-thing] #'magithub-comment-new)
    (define-key map "L" #'magithub-issue-add-labels)
    (define-key map "N" #'magithub-issue-personal-note)
    map)
  "Keymap for `magithub-issue' sections.")

(defvar magit-magithub-issues-list-section-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map magithub-map)
    (define-key map [remap magit-visit-thing] #'magithub-issue-visit)
    (define-key map [remap magithub-browse-thing] #'magithub-issue-browse)
    map)
  "Keymap for `magithub-issue-list' sections.")

(defvar magit-magithub-pull-request-section-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map magithub-map)
    (define-key map [remap magit-visit-thing] #'magithub-pull-visit)
    (define-key map [remap magithub-browse-thing] #'magithub-pull-browse)
    (define-key map "L" #'magithub-issue-add-labels)
    map)
  "Keymap for `magithub-pull-request' sections.")

(defvar magit-magithub-pull-requests-list-section-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map magithub-map)
    (define-key map [remap magit-visit-thing] #'magithub-pull-visit)
    (define-key map [remap magithub-browse-thing] #'magithub-pull-browse)
    map)
  "Keymap for `magithub-pull-request-list' sections.")

;;; By maintaining these as lists of functions, we're setting
;;; ourselves up to be able to dynamically apply new filters from the
;;; status buffer (e.g., 'bugs' or 'questions' assigned to me)
(defcustom magithub-issue-issue-filter-functions nil
  "List of functions that filter issues.
Each function will be supplied a single issue object.  If any
function returns nil, the issue will not be listed in the status
buffer."
  :type '(repeat function)
  :group 'magithub)

(defcustom magithub-issue-pull-request-filter-functions nil
  "List of functions that filter pull-requests.
Each function will be supplied a single issue object.  If any
function returns nil, the issue will not be listed in the status
buffer."
  :type '(repeat function)
  :group 'magithub)

(defun magithub-issue-add-labels (issue labels)
  "Update ISSUE's labels to LABELS."
  (interactive
   (when (magithub-verify-manage-labels t)
     (let* ((fmt (lambda (l) (alist-get 'name l)))
            (issue (or (magithub-thing-at-point 'issue)
                       (magithub-thing-at-point 'pull-request)))
            (current-labels (alist-get 'labels issue))
            (to-remove (magithub--completing-read-multiple
                        "Remove labels: " current-labels fmt)))
       (setq current-labels (cl-set-difference current-labels to-remove))
       (list issue (magithub--completing-read-multiple
                    "Add labels: " (magithub-label-list) fmt
                    nil nil current-labels)))))
  (when (ghubp-patch-repos-owner-repo-issues-number
         (magithub-repo) issue `((labels . ,labels)))
    (setcdr (assq 'labels issue) labels))
  (when (derived-mode-p 'magit-status-mode)
    (magit-refresh)))

(defun magithub-issue--insert-issue-section ()
  "Insert GitHub issues if appropriate."
  (when (and (magithub-usable-p)
             (alist-get 'has_issues (magithub-repo)))
    (magithub-issue--insert-generic-section
     (magithub-issues-list)
     "Issues"
     (magithub-issues)
     magithub-issue-issue-filter-functions)))

(defun magithub-issue--insert-pr-section ()
  "Insert GitHub pull requests if appropriate."
  (when (magithub-usable-p)
    (magithub-feature-maybe-idle-notify
     'pull-request-merge
     'pull-request-checkout)
    (magithub-issue--insert-generic-section
     (magithub-pull-requests-list)
     "Pull Requests"
     (magithub-pull-requests)
     magithub-issue-pull-request-filter-functions)))

(defmacro magithub-issue--insert-generic-section
    (spec title list filters)
  (let ((sym-filtered (cl-gensym)))
    `(when-let ((,sym-filtered (magithub-filter-all ,filters ,list)))
       (magit-insert-section ,spec
         (insert (format "%s%s:"
                         (propertize ,title 'face 'magit-header-line)
                         (if ,filters
                             (propertize " (filtered)" 'face 'magit-dimmed)
                           "")))
         (magit-insert-heading)
         (magithub-issue-insert-sections ,sym-filtered)
         (insert ?\n)))))

(defun magithub-issue-browse (issue)
  "Visits ISSUE in the browser.
Interactively, this finds the issue at point."
  (interactive (list (magithub-interactive-issue)))
  (magithub-issue--browse issue))

(defun magithub-issue-visit (issue)
  "Visits ISSUE in Emacs.
Interactively, this finds the issue at point."
  (interactive (list (magithub-interactive-issue)))
  (magithub-issue-view issue))

(defun magithub-pull-browse (pr)
  "Visits PR in the browser.
Interactively, this finds the pull request at point."
  (interactive (list (magithub-interactive-pull-request)))
  (magithub-issue--browse pr))

(defun magithub-pull-visit (pr)
  "Visits PR in Emacs.
Interactively, this finds the pull request at point."
  (interactive (list (magithub-interactive-pull-request)))
  (magithub-issue-view pr))

(defun magithub-issue--browse (issue-or-pr)
  "Visits ISSUE-OR-PR in the browser.
Interactively, this finds the issue at point."
  (when-let ((url (alist-get 'html_url issue-or-pr)))
    (browse-url url)))

(defun magithub-repolist-column-issue (_id)
  "Insert the number of open issues in this repository."
  (when (magithub-usable-p)
    (number-to-string (length (magithub-issues)))))

(defun magithub-repolist-column-pull-request (_id)
  "Insert the number of open pull requests in this repository."
  (when (magithub-usable-p)
    (number-to-string (length (magithub-pull-requests)))))

(magithub--deftoggle magithub-toggle-pull-requests "pull requests" t
  magit-status-sections-hook #'magithub-issue--insert-pr-section)
(magithub--deftoggle magithub-toggle-issues "issues" t
  magit-status-sections-hook #'magithub-issue--insert-issue-section)

;; Pull Request handling

(defun magithub-pull-request (repo number)
  "Retrieve a pull request in REPO by NUMBER."
  (magithub-cache :issues
    `(ghubp-get-repos-owner-repo-pulls-number
      ',repo '((number . ,number)))
    :message
    (format "Getting pull request %s#%d..."
            (magithub-repo-name repo)
            number)))

(defun magithub-remote-fork-p (remote)
  "True if REMOTE is a fork."
  (thread-last remote
    (magithub-repo-from-remote)
    (alist-get 'fork)))

(defun magithub-pull-request-checked-out (pull-request)
  "True if PULL-REQUEST is currently checked out."
  (let-alist pull-request
    (let ((remote .user.login)
          (branch .head.ref))
      (and (magit-remote-p remote)
           (magithub-remote-fork-p remote)
           (magit-branch-p branch)
           (string= remote (magit-get-push-remote branch))))))

(defun magithub-pull-request-checkout (pull-request)
  "Checkout PULL-REQUEST.
PULL-REQUEST is the full object; not just the issue subset."
  (interactive (list
                (let ((pr (or (magithub-thing-at-point 'pull-request)
                              (magithub-issue-completing-read-pull-requests))))
                  (ghubp-get-repos-owner-repo-pulls-number
                   (magithub-repo)
                   `((number . ,(alist-get 'number pr)))))))
  (let-alist pull-request
    (let ((remote .user.login)
          (branch (format "%s/%s" .user.login .head.ref)))
      (cond
       ((magithub-pull-request-checked-out pull-request)
        (with-temp-message (format "PR#%d is already checked out somewhere; checking out %s"
                                   .number branch)
          (magit-checkout branch)
          (magit-fetch remote (magit-fetch-arguments))))
       ((magit-branch-p branch)
        (user-error "Cannot checkout pull request: branch `%s' already exists; rename branch on remote" branch))
       (t
        (magithub--run-git-synchronously
         ;; get remote
         (unless (magit-remote-p remote)
           (magit-remote-add remote (magithub-repo--clone-url .head.repo)))
         (magit-fetch remote (magit-fetch-arguments))
         ;; create branch
         (magit-git-success "branch" branch .base.sha)  ; also sets upstream to base ref
         ;; set push to remote branch
         (magit-set (concat "refs/heads/" .base.ref) "branch" branch "merge")
         (magit-set "." "branch" branch "remote") ;same as merge
         (magit-set remote "branch" branch "pushRemote")
         (magit-set (number-to-string .number) "branch" branch "magithub" "sourcePR")
         ;; set descripiton
         (magit-set (concat "PR: " .title) "branch" branch "description")
         ;; Checkout
         (magit-git-success "checkout" branch)
         (magit-refresh)))))))

(provide 'magithub-issue)
;;; magithub-issue.el ends here
