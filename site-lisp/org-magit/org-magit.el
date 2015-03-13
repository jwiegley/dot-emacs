;;; org-magit.el --- basic support for magit links

;; Copyright (C) 2011, 2012  Yann Hodique.

;; Author: Yann Hodique <yann.hodique@gmail.com>
;; Keywords: git, magit, outlines
;; Version: 0.2.0
;; Package-Requires: ((magit "0.8") (org "6.01"))

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; This module adds support for magit links in org buffers. The following links
;; are supported:
;; - magit:/path/to/repo::commit@<hash>
;; - magit:/path/to/repo::status
;; - magit:/path/to/repo::log

;; Of course those links can be stored as usual with `org-store-link' from the
;; corresponding magit buffers. By default the path to the repo is abbreviated
;; with `abbreviate-file-name', just like org-mode does. See
;; `directory-abbrev-alist' for configuring its behavior. Alternately, you can
;; customize `org-magit-filename-transformer' and provide your own
;; transformer function.

;; When exporting those links, the variable `org-magit-known-public-providers'
;; is used to generate meaningful links. This assumes there exists a public
;; http server that is able to expose those objects.

;; Certain settings can be configured directly at the repository level
;; if needed. For example
;;
;; $ git config org-magit.remote upstream
;;
;; In this case, html links will point to the "upstream" webserver, instead of
;; the default "origin". URL templates can also be stored in the
;; repository. For example
;;
;; $ git config org-magit.log http://myserver/plop.git/history

;;; Code:

(eval-when-compile
  (require 'cl))

(require 'org)
(require 'magit)

(defvar org-magit-actions
  '((status :open current-buffer)
    (log :open org-magit-open-log)
    (commit :open org-magit-open-commit)))

(defgroup org-magit nil
  "Magit links for org-mode"
  :group 'magit
  :group 'org-link)

(defcustom org-magit-public-remote "origin"
  "Default remote to use when exporting links."
  :group 'org-magit
  :type 'string)

(defcustom org-magit-config-prefix "org-magit"
  "Section to read from in git repository configuration."
  :group 'org-magit
  :type 'string)

(defun org-magit-gitweb-provider (base)
  `(status ,(concat base "/?p=\\1;a=summary")
           log ,(concat base "/?p=\\1;a=log")
           commit ,(concat base "/?p=\\1;a=commit;h=%s")))

(defun org-magit-gitorious-provider (base)
  `(status ,(concat base "/\\1")
           log ,(concat base "/\\1/commits")
           commit ,(concat base "/\\1/commit/%s")))

(defcustom org-magit-known-public-providers
  `(;; GitHub
    (,(rx bol (or "git@github.com:"
                  (and (or "git" "ssh" "http" "https") "://"
                       (* nonl) (? "@") "github.com/"))
          (group (* nonl)) ".git")
     status "https://github.com/\\1/"
     log "https://github.com/\\1/commits"
     commit "https://github.com/\\1/commit/%s")
    ;; Gitorious
    (,(rx bol (or "git@gitorious.org:"
                  (and (or "git://gitorious.org/"
                           (and
                            (or "http" "https")
                            "://git.gitorious.org/"))))
          (group (* nonl)) ".git")
     ,@(org-magit-gitorious-provider "https://gitorious.org"))
    ;; Bitbucket
    (,(rx bol (or "git@bitbucket.org:"
                  (and (or "ssh" "http" "https") "://"
                       (* nonl) (? "@") "bitbucket.org")) (group (* nonl)))
     status "https://bitbucket.org/\\1"
     log "https://bitbucket.org/\\1/changesets"
     commit "https://bitbucket.org/\\1/changeset/%s")
    ;; org-mode
    (,(rx bol "git://orgmode.org/" (group (* nonl) ".git"))
     ,@(org-magit-gitweb-provider "http://orgmode.org/w"))
    ;; kernel.org
    (,(rx bol (or "git" "http" "https") "://git.kernel.org/pub/scm/"
          (group (* nonl) ".git"))
     ,@(org-magit-gitweb-provider "http://git.kernel.org")))
  "List of git providers, and how to generate links for each
  object category."
  :group 'org-magit
  :type '(repeat (list :tag "Provider identifier" regexp
                       (set :tag "URL templates" :inline t
                            (list :inline t
                                  (const :tag "Status" status)
                                  (string :tag "Status URL"))
                            (list :inline t
                                  (const :tag "Log" log)
                                  (string :tag "Log URL"))
                            (list :inline t
                                  (const :tag "Commit" commit)
                                  (string :tag "Commit URL"))))))

(defcustom org-magit-filename-transformer
  'abbreviate-file-name
  "Function to call to produce canonical repository name. This
must take a path as input, and provide an equivalent
representation of this path as output."
  :group 'org-magit
  :type 'function)

(defun org-magit-split-string (str)
  (let* ((strlist (split-string str "::"))
         (repo (first strlist))
         (view (second strlist))
         (view-sym nil)
         (args nil))
    (cond ((string-match "^status" view)
           (setq view-sym 'status))
          ((string-match "^log" view)
           (setq view-sym 'log))
          ((string-match "^commit@\\(.*\\)" view)
           (setq view-sym 'commit
                 args (list (match-string 1 view)))))
    (list view-sym repo args)))

(defun org-magit-open-log ()
  (let ((buffer (current-buffer)))
    (funcall (if (fboundp 'magit-log) 'magit-log 'magit-display-log))
    (bury-buffer buffer)
    (current-buffer)))

(defun org-magit-open-commit (commit)
  (let ((buffer (current-buffer)))
    (magit-show-commit commit)
    (bury-buffer buffer)
    (get-buffer magit-commit-buffer-name)))

;;;###autoload
(defun org-magit-open (str)
  (let* ((split (org-magit-split-string str))
         (view (first split))
         (repo (second split))
         (func (plist-get (cdr (assoc view org-magit-actions)) :open))
         (args (third split)))
    (when func
      (pop-to-buffer
       (save-window-excursion
         (magit-status repo)
         (apply func args))))))

(defun org-magit-get (repo &rest keys)
  (let ((default-directory repo))
    (apply 'magit-get keys)))

(defun org-magit-guess-public-url (view url)
  (let ((res nil))
    (when url
      (dolist (provider org-magit-known-public-providers)
        (let ((regexp (car provider)))
          (when (string-match regexp url)
            (setq res (replace-match (plist-get (cdr provider) view)
                                     nil nil url))))))
    res))

(defun org-magit-generate-public-url (path)
  (let* ((split (org-magit-split-string path))
         (view (first split))
         (repo (second split))
         (remote (or (org-magit-get
                      repo (format "%s.remote" org-magit-config-prefix))
                     org-magit-public-remote))
         remote-repo
         (tpl (or (org-magit-get
                   repo (format "%s.%s" org-magit-config-prefix view))
                  (org-magit-guess-public-url
                   view (setq remote-repo
                              (org-magit-get
                               repo (format "remote.%s.url" remote)))))))
    (or (and tpl
             (apply 'format tpl (third split)))
        (and remote-repo
             (concat remote-repo (when (third split)
                                   (concat "@"
                                           (mapconcat 'identity
                                                      (third split) "@")))))
        (and (featurep 'magit-svn)
             (let* ((default-directory repo)
                    (info (magit-svn-get-ref-info)))
               (and info
                    (cdr (assoc 'url info)))))
        path)))

;;;###autoload
(defun org-magit-export (path desc format)
  (let ((url (or (org-magit-generate-public-url path) path)))
    (set-text-properties 0 (length url) nil url)
    (set-text-properties 0 (length desc) nil desc)
    (cond
     ((eq format 'html) (format "<a href=\"%s\">%s</a>" url (or desc url)))
     ((eq format 'latex) (format "\\href{%s}{%s}" url (or desc url)))
     (t (or desc url)))))

(defun org-magit-make-link (repo &rest components)
  (apply 'concat "magit:" repo components))

(defun org-magit-clean-repository (repo)
  (let ((name (file-name-nondirectory (directory-file-name repo))))
    (when (not (string-match "\\.git" name))
      (setq name (concat name ".git")))
    name))

;; magit used to have only one major-mode: magit-mode, and minor-modes for
;; status, log and commit. Now they are all major-modes deriving from
;; magit-mode. Let's have a backward-compatible check for the
;; current magit mode.
(defmacro org-magit-check-mode (mode)
  `(or (and (boundp ',mode) ,mode)
       (derived-mode-p ',mode)))

;;;###autoload
(defun org-magit-store-link ()
  (when (derived-mode-p 'magit-mode)
    (let* ((repo (or (and org-magit-filename-transformer
                          (funcall org-magit-filename-transformer
                                   default-directory))
                     default-directory))
           (link nil)
           (description (org-magit-clean-repository repo)))
      (cond ((org-magit-check-mode magit-status-mode)
             (setq link (org-magit-make-link repo "::status")
                   description (format "%s status" description)))
            ((org-magit-check-mode magit-log-mode)
             (setq link (org-magit-make-link repo "::log")
                   description (format "%s log" description)))
            ((org-magit-check-mode magit-commit-mode)
             (let ((short-sha (if (> (length magit-currently-shown-commit) 8)
                                  (substring magit-currently-shown-commit
                                             0 8)
                                magit-currently-shown-commit)))
               (setq link
                     (org-magit-make-link repo "::commit@"
                                          magit-currently-shown-commit)
                     description (format "%s commit #%s" description
                                         short-sha)))))

      (org-store-link-props
       :type "magit"
       :link link
       :description description))))

;;;###autoload
(eval-after-load "org"
  '(progn
     (org-add-link-type "magit" 'org-magit-open 'org-magit-export)
     (add-hook 'org-store-link-functions 'org-magit-store-link)))

(provide 'org-magit)
;;; org-magit.el ends here
