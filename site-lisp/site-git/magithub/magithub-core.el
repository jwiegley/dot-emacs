;;; magithub-core.el --- core functions for magithub  -*- lexical-binding: t; -*-

;; Copyright (C) 2016  Sean Allred

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

;;

;;; Code:

(require 'magit)
(require 'dash)
(require 's)

(defun magithub-github-repository-p ()
  "Non-nil if \"origin\" points to GitHub or a whitelisted domain."
  (-when-let (origin (magit-get "remote" "origin" "url"))
    (-some? (lambda (domain) (s-contains? domain origin))
            (cons "github.com" (magit-get-all "hub" "host")))))

(defun magithub-repo-id ()
  "Returns an identifying value for this repository."
  (magit-get "remote" "origin" "url"))

(defun magithub--api-available-p ()
  "Non-nil if the API is available."
  (let ((magit-git-executable "ping")
        (magit-pre-call-git-hook nil)
        (magit-git-global-arguments nil))
    (= 0 (magit-git-exit-code "-c 1" "-n" "api.github.com"))))

(defun magithub--completing-read-multiple (prompt collection)
  "Using PROMPT, get a list of elements in COLLECTION.
This function continues until all candidates have been entered or
until the user enters a value of \"\".  Duplicate entries are not
allowed."
  (let (label-list this-label done)
    (while (not done)
      (setq collection (remove this-label collection)
            this-label "")
      (when collection
        ;; @todo it would be nice to detect whether or not we are
        ;; allowed to create labels -- if not, we can require-match
        (setq this-label (completing-read prompt collection)))
      (unless (setq done (s-blank? this-label))
        (push this-label label-list)))
    label-list))

(defconst magithub-hash-regexp
  (rx bow (= 40 (| digit (any (?A . ?F) (?a . ?f)))) eow)
  "Regexp for matching commit hashes.")

(defcustom magithub-hub-executable "hub"
  "The hub executable used by Magithub."
  :group 'magithub
  :package-version '(magithub . "0.1")
  :type 'string)

(defvar magithub-debug-mode nil
  "When non-nil, echo hub commands before they're executed.")

(defvar magithub-hub-error nil
  "When non-nil, this is a message for when hub fails.")

(defmacro magithub-with-hub (&rest body)
  `(let ((magit-git-executable magithub-hub-executable)
         (magit-pre-call-git-hook nil)
         (magit-git-global-arguments nil))
     ,@body))

(defun magithub--hub-command (magit-function command args)
  (unless (executable-find magithub-hub-executable)
    (user-error "Hub (hub.github.com) not installed; aborting"))
  (unless (file-exists-p "~/.config/hub")
    (user-error "Hub hasn't been initialized yet; aborting"))
  (when magithub-debug-mode
    (message "Calling hub with args: %S %S" command args))
  (with-timeout (5 (error "Took too long!  %s%S" command args))
    (magithub-with-hub (funcall magit-function command args))))

(defun magithub--git-raw-output (&rest args)
  "Execute Git with ARGS, returning its output as string.
Adapted from `magit-git-lines'."
  (with-temp-buffer
    (apply #'magit-git-insert args)
    (buffer-string)))

(defun magithub--command (command &optional args)
  "Run COMMAND synchronously using `magithub-hub-executable'."
  (magithub--hub-command #'magit-run-git command args))

(defun magithub--command-with-editor (command &optional args)
  "Run COMMAND asynchronously using `magithub-hub-executable'.
Ensure GIT_EDITOR is set up appropriately."
  (magithub--hub-command #'magit-run-git-with-editor command args))

(defun magithub--command-output (command &optional args raw)
  "Run COMMAND synchronously using `magithub-hub-executable'.
If not RAW, return output as a list of lines."
  (magithub--hub-command (if raw #'magithub--git-raw-output #'magit-git-lines) command args))

(defun magithub--command-quick (command &optional args)
  "Quickly execute COMMAND with ARGS."
  (ignore (magithub--command-output command args)))

(defun magithub-hub-version ()
  "Return the `hub' version as a string."
  (-> "--version"
      magithub--command-output cadr
      split-string cddr car
      (split-string "-") car))

(defun magithub-hub-version-at-least (version-string)
  "Return t if `hub's version is at least VERSION-STRING."
  (version<= version-string (magithub-hub-version)))

(defun magithub--meta-new-issue ()
  "Open a new Magithub issue.
See /.github/ISSUE_TEMPLATE.md in this repository."
  (interactive)
  (browse-url "https://github.com/vermiculus/magithub/issues/new"))

(defun magithub--meta-help ()
  "Open Magithub help."
  (interactive)
  (browse-url "https://gitter.im/vermiculus/magithub"))

(defun magithub-enable ()
  "Enable Magithub for this repository."
  (interactive)
  (magit-set "yes" "magithub" "enabled")
  (when (derived-mode-p 'magit-status-mode)
    (magit-refresh)))

(defun magithub-disable ()
  "Disable Magithub for this repository."
  (interactive)
  (magit-set "no" "magithub" "enabled")
  (when (derived-mode-p 'magit-status-mode)
    (magit-refresh)))

(defun magithub-enabled-p ()
  "Returns non-nil when Magithub is enabled for this repository."
  (when (member (magit-get "magithub" "enabled") '("yes" nil)) t))

(defun magithub-enabled-toggle ()
  "Toggle Magithub"
  (interactive)
  (if (magithub-enabled-p)
      (magithub-disable)
    (magithub-enable)))

(defun magithub-usable-p ()
  "Non-nil if Magithub should do its thing."
  (and (executable-find magithub-hub-executable)
       (magithub-enabled-p)
       (magithub-github-repository-p)
       (magithub--api-available-p)))

(defun magithub-error (err-message tag &optional trace)
  "Report a Magithub error."
  (setq trace (or trace (with-output-to-string (backtrace))))
  (when (y-or-n-p (concat tag "  Report?  (A bug report will be placed in your clipboard.)"))
    (with-current-buffer-window
     (get-buffer-create "*magithub issue*")
     #'display-buffer-pop-up-window nil
     (when (fboundp 'markdown-mode) (markdown-mode))
     (insert
      (kill-new
       (format
        "## Automated error report

### Description

%s

### Backtrace

```
%s```
"
        (read-string "Briefly describe what you were doing: ")
        trace))))
    (magithub--meta-new-issue))
  (error err-message))

(defmacro magithub--deftoggle (name hook func s)
  "Define a section-toggle command."
  (declare (indent defun))
  `(defun ,name ()
     ,(concat "Toggle the " s " section.")
     (interactive)
     (if (memq ,func ,hook)
         (remove-hook ',hook ,func)
       (if (executable-find magithub-hub-executable)
           (add-hook ',hook ,func t)
         (message ,(concat "`hub' isn't installed, so I can't insert " s))))
     (when (derived-mode-p 'magit-status-mode)
       (magit-refresh))
     (memq ,func ,hook)))

(defun magithub--zip-case (p e)
  "Get an appropriate value for element E given property/function P."
  (cond
   ((symbolp p) (plist-get e p))
   ((functionp p) (funcall p e))
   ((null p) e)
   (t nil)))

(defun magithub--zip (object-list prop1 prop2)
  "Process OBJECT-LIST into an alist defined by PROP1 and PROP2.

If a prop is a symbol, that property will be used.

If a prop is a function, it will be called with the
current element of OBJECT-LIST.

If a prop is nil, the entire element is used."
  (delq nil
        (-zip-with
         (lambda (e1 e2)
           (let ((p1 (magithub--zip-case prop1 e1))
                 (p2 (magithub--zip-case prop2 e2)))
             (unless (or (and prop1 (not p1))
                         (and prop2 (not p2)))
               (cons (if prop1 p1 e1)
                     (if prop2 p2 e2)))))
         object-list object-list)))

(provide 'magithub-core)
;;; magithub-core.el ends here
