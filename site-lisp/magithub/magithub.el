;;; magithub.el --- Magit interfaces for Github  -*- lexical-binding: t; -*-

;; Copyright (C) 2016-2017  Sean Allred

;; Author: Sean Allred <code@seanallred.com>
;; Keywords: git, tools, vc
;; Homepage: https://github.com/vermiculus/magithub
;; Package-Requires: ((emacs "25") (magit "2.8") (s "1.12.0") (ghub+ "0.2") (git-commit "2.8") (markdown-mode "2.3"))
;; Package-Version: 0.1.4

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

;; Magithub is a Magit-based interface to Github.
;;
;; Integrated into Magit workflows, Magithub allows easy Github
;; repository management.  Supported actions include:
;;
;;  - pushing brand-new local repositories up to Github
;;  - creating forks of existing repositories
;;  - submitting pull requests upstream
;;  - viewing and creating issues
;;  - seeing status checks
;;
;; all from the `magit-status' buffer.
;;
;; Press `H' in the status buffer to get started -- happy hacking!

;;; Code:

(require 'magit)
(require 'magit-process)
(require 'magit-popup)
(require 'cl-lib)
(require 's)
(require 'dash)
(require 'ghub+)

(require 'magithub-core)
(require 'magithub-issue)
(require 'magithub-ci)
(require 'magithub-proxy)
(require 'magithub-issue-post)
(require 'magithub-issue-tricks)
(require 'magithub-orgs)
(require 'magithub-dash)

;;;###autoload (autoload 'magithub-dispatch-popup "magithub" nil t)
(magit-define-popup magithub-dispatch-popup
  "Popup console for dispatching other Magithub popups."
  'magithub-commands
  :actions '("Actions"
             (?d "Dashboard" magithub-dashboard)
             (?H "Browse on Github" magithub-browse)
             (?c "Create" magithub-create)
             (?f "Fork" magithub-fork)
             (?i "Issues" magithub-issue-new)
             (?p "Submit a pull request" magithub-pull-request-new)
             (?x "Use a proxy repository for issues/PRs" magithub-proxy-set)
             (?O "Toggle online/offline" magithub-toggle-online)
             "Meta"
             (?` "Toggle Magithub-Status integration" magithub-enabled-toggle)
             (?~ "Toggle CI status header" magithub-ci-toggle)
             (?& "Request a feature or report a bug" magithub--meta-new-issue)
             (?h "Ask for help on Gitter" magithub--meta-help)))

(eval-after-load "magit"
  '(progn
     (magit-define-popup-action 'magit-dispatch-popup
       ?H "Magithub" #'magithub-dispatch-popup ?!)
     (define-key magit-status-mode-map
       "H" #'magithub-dispatch-popup)))

(defun magithub-browse ()
  "Open the repository in your browser."
  (interactive)
  (unless (magithub-github-repository-p)
    (user-error "Not a Github repository"))
  (magithub-repo-visit (magithub-repo)))

(defvar magithub-after-create-messages
  '("Don't be shy!"
    "Don't let your dreams be dreams!")
  "One of these messages will be displayed after you create a
Github repository.")

(defun magithub-create (repo &optional org)
  "Create REPO on Github.

If ORG is non-nil, it is an organization object under which to
create the new repository.  You must be a member of this
organization."
  (interactive (if (or (not (magit-toplevel)) (magithub-github-repository-p))
                   (list nil nil)
                 (let* ((ghub-username (ghubp-username)) ;performance
                        (account (magithub--read-user-or-org))
                        (priv (yes-or-no-p "Will this be a private repository? "))
                        (reponame (magithub--read-repo-name account))
                        (desc (read-string "Description (optional): ")))
                   (list
                    `((name . ,reponame)
                      (private . ,priv)
                      (description . ,desc))
                    (unless (string= ghub-username account)
                      `((login . ,account)))))))
  (when (magithub-github-repository-p)
    (error "Already in a Github repository"))
  (if (not (magit-toplevel))
      (when (y-or-n-p "Not inside a Git repository; initialize one here? ")
        (magit-init default-directory)
        (call-interactively #'magithub-create))
    (with-temp-message "Creating repository on Github..."
      (setq repo
            (magithub-request
             (if org
                 (ghubp-post-orgs-org-repos org repo)
               (ghubp-post-user-repos repo)))))
    (magithub--random-message "Creating repository on Github...done!")
    (magit-status-internal default-directory)
    (magit-remote-add "origin" (magithub-repo--clone-url repo))
    (magit-refresh)
    (when (magit-rev-verify "HEAD")
      (magit-push-popup))))

(defun magithub--read-user-or-org ()
  "Prompt for an account with completion.

Candidates will include the current user and all organizations,
public and private, of which they're a part.  If there is only
one candidate (i.e., no organizations), the single candidate will
be returned without prompting the user."
  (let ((user (ghubp-username))
        (orgs (ghubp-get-in-all '(login)
                (magithub-orgs-list)))
        candidates)
    (setq candidates orgs)
    (when user (push user candidates))
    (cl-case (length candidates)
      (0 (user-error "No accounts found"))
      (1 (car candidates))
      (t (completing-read "Account: " candidates nil t)))))

(defun magithub--read-repo-name (for-user)
  (let* ((prompt (format "Repository name: %s/" for-user))
         (dirnam (file-name-nondirectory (substring default-directory 0 -1)))
         (valid-regexp (rx bos (+ (any alnum "." "-" "_")) eos))
         ret)
    ;; This is not very clever, but it gets the job done.  I'd like to
    ;; either have instant feedback on what's valid or not allow users
    ;; to enter invalid names at all.  Could code from Ivy be used?
    (while (not (s-matches-p valid-regexp (setq ret (read-string prompt nil nil dirnam))))
      (message "invalid name")
      (sit-for 1))
    ret))

(defun magithub--random-message (&optional prefix)
  (let ((msg (nth (random (length magithub-after-create-messages))
                  magithub-after-create-messages)))
    (if prefix (format "%s  %s" prefix msg) msg)))

(defun magithub-fork ()
  "Fork 'origin' on Github."
  (interactive)
  (unless (magithub-github-repository-p)
    (user-error "Not a Github repository"))
  (let* ((repo (magithub-repo))
         (fork (with-temp-message "Forking repository on Github..."
                 (magithub-request
                  (ghubp-post-repos-owner-repo-forks repo)))))
    (when (y-or-n-p "Create a spinoff branch? ")
      (call-interactively #'magit-branch-spinoff))
    (magithub--random-message
     (let-alist repo (format "%s/%s forked!" .owner.login .name)))
    (let-alist fork
      (when (y-or-n-p (format "Add %s as a remote in this repository? " .owner.login))
        (magit-remote-add .owner.login (magithub-repo--clone-url fork))
        (magit-set .owner.login "branch" (magit-get-current-branch) "pushRemote")))
    (let-alist repo
      (when (y-or-n-p (format "Set upstream to %s? " .owner.login))
        (call-interactively #'magit-set-branch*merge/remote)))))

(defun magithub-clone--get-repo ()
  "Prompt for a user and a repository.
Returns a sparse repository object."
  (let ((user (ghubp-username))
        (repo-regexp  (rx bos (group (+ (not (any " "))))
                          "/" (group (+ (not (any " ")))) eos))
        repo)
    (while (not (and repo (string-match repo-regexp repo)))
      (setq repo (read-from-minibuffer
                  (concat
                   "Clone Github repository "
                   (if repo "(format is \"user/repo\"; C-g to quit)" "(user/repo)")
                   ": ")
                  (when user (concat user "/")))))
    `((owner (login . ,(match-string 1 repo)))
      (name . ,(match-string 2 repo)))))

(defcustom magithub-clone-default-directory nil
  "Default directory to clone to when using `magithub-clone'.
When nil, the current directory at invocation is used."
  :type 'directory
  :group 'magithub)

(defun magithub-clone (repo dir)
  "Clone REPO.
Banned inside existing Github repositories if
`magithub-clone-default-directory' is nil.

See also `magithub-preferred-remote-method'."
  (interactive (if (and (not magithub-clone-default-directory)
                        (magithub-github-repository-p))
                   (user-error "Already in a Github repo")
                 (let ((repo (magithub-clone--get-repo)))
                   (condition-case _
                       (let* ((repo (magithub-request
                                     (ghubp-get-repos-owner-repo repo)))
                              (dirname (read-directory-name
                                        "Destination: "
                                        magithub-clone-default-directory
                                        (alist-get 'name repo))))
                         (list repo dirname))
                     (ghub-404 (let-alist repo
                                 (user-error "Repository %s/%s does not exist"
                                             .owner.login .name)))))))
  ;; Argument validation
  (unless (called-interactively-p 'any)
    (condition-case _
        (setq repo (magithub-request
                    (ghubp-get-repos-owner-repo repo)))
      (ghub-404
       (let-alist repo
         (user-error "Repository %s/%s does not exist"
                     .owner.login .name)))))
  (unless (file-writable-p dir)
    (user-error "%s does not exist or is not writable" dir))

  (let-alist repo
    (when (y-or-n-p (format "Clone %s to %s? " .full_name dir))
      (let ((default-directory dir)
            (magit-clone-set-remote.pushDefault t)
            set-upstream set-proxy)

        (setq set-upstream
              (and .fork (y-or-n-p (format (concat "This repository appears to be a fork of %s; "
                                                   "set upstream to that remote?")
                                           .parent.full_name)))
              set-proxy
              (and set-upstream (y-or-n-p "Use upstream as a proxy for issues, etc.? ")))

        (condition-case _
            (progn
              (mkdir dir t)
              (magit-clone (magithub-repo--clone-url repo) dir)
              (while (process-live-p magit-this-process)
                (magit-process-buffer)
                (message "Waiting for clone to finish...")
                (sit-for 1))
              (when set-upstream
                (let ((upstream "upstream"))
                  (when set-proxy (magithub-proxy-set upstream))
                  (magit-remote-add upstream (magithub-repo--clone-url .parent))
                  (magit-set-branch*merge/remote (magit-get-current-branch) upstream)))))))))

(defun magithub-clone--finished (user repo dir)
  "After finishing the clone, allow the user to jump to their new repo."
  (when (y-or-n-p (format "%s/%s has finished cloning to %s.  Open? " user repo dir))
    (magit-status-internal (s-chop-suffix "/" dir))))

(defun magithub-feature-autoinject (feature)
  "Configure FEATURE to recommended settings.
If FEATURE is `all' or t, all known features will be loaded.

Features:

- `pull-request-merge'
  (`magithub-pull-request-merge' inserted into `magit-am-popup')

- `pull-request-checkout'
  (`magithub-pull-request-checkout' inserted into `magit-branch-popup')"
  (if (memq feature '(t all))
      (mapc #'magithub-feature-autoinject magithub-feature-list)
    (cl-case feature

      (pull-request-merge
       (magit-define-popup-action 'magit-am-popup
         ?P "Apply patches from pull request" #'magithub-pull-request-merge))

      (pull-request-checkout
       (magit-define-popup-action 'magit-branch-popup
         ?P "Checkout pull request" #'magithub-pull-request-checkout))

      (t (user-error "unknown feature %S" feature)))
    (add-to-list 'magithub-features (cons feature t))))

(defun magithub-visit-thing ()
  (interactive)
  (user-error
   (with-temp-buffer
     (use-local-map magithub-map)
     (substitute-command-keys
      "Deprecated; use `\\[magithub-browse-thing]' instead"))))

(provide 'magithub)
;;; magithub.el ends here
