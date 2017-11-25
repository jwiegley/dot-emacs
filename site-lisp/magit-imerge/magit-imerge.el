;;; magit-imerge.el --- Magit extension for git-imerge  -*- lexical-binding: t; -*-

;; Copyright (C) 2017  Kyle Meyer

;; Author: Kyle Meyer <kyle@kyleam.com>
;; URL: https://github.com/magit/magit-imerge
;; Keywords: vc, tools
;; Version: 0.2.0
;; Package-Requires: ((emacs "24.4") (magit "2.10.0"))

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Magit-imerge is a Magit interface to git-imerge [*], a Git
;; extension for performing incremental merges.
;;
;; There are four high-level git-imerge subcommands that can be used
;; to start an incremental merge.  Each has a corresponding command in
;; Magit-imerge.
;;
;;   * git-imerge merge  => magit-imerge-merge
;;   * git-imerge rebase => magit-imerge-rebase
;;   * git-imerge revert => magit-imerge-revert
;;   * git-imerge drop   => magit-imerge-drop
;;
;; All these commands are available under the popup
;; `magit-imerge-popup', which by default is bound to "i" in the main
;; merge popup.
;;
;; Once an incremental merge has been started with one of the commands
;; above, the imerge popup will display the following sequence
;; commands:
;;
;;   * magit-imerge-continue
;;   * magit-imerge-suspend
;;   * magit-imerge-finish
;;   * magit-imerge-abort
;;
;; One of the advantages of incremental merges is that you can return
;; to them at a later time.  Calling `magit-imerge-suspend' will
;; suspend the current incremental merge.  You can resume it later
;; using `magit-imerge-resume'.
;;
;; When Magit-imerge is installed from MELPA, no additional setup is
;; needed beyond installing git-imerge.  The imerge popup will be
;; added under the Magit merge popup, and Magit-imerge will be loaded
;; the first time that the imerge popup is invoked.
;;
;; [*] https://github.com/mhagger/git-imerge

;;; Code:

(require 'dash)
(require 'magit)
(require 'json)

;;; Options

(defgroup magit-imerge nil
  "Magit extension for git-imerge"
  :prefix "magit-imerge"
  :group 'magit-extensions)

(defface magit-imerge-overriding-value
  '((t (:inherit font-lock-warning-face)))
  "Face used in status buffer for an overriding state option."
  :group 'magit-imerge)

;;; Utilities

(defun magit-imerge-names ()
  "List all the incremental merges in the current repository."
  (delq nil (--map (and (string-match "\\`refs/imerge/\\(.+\\)/state\\'" it)
                        (match-string 1 it))
                   (magit-list-refs "refs/imerge/"))))

(defun magit-imerge-state (name)
  "Return the state of incremental merge NAME."
  (--when-let (magit-rev-verify (format "refs/imerge/%s/state" name))
    (json-read-from-string (magit-git-string "cat-file" "blob" it))))

(defun magit-imerge--default-name ()
  "Return the configured imerge name, if it exists."
  (--when-let (magit-get "imerge.default")
    (and (magit-rev-verify (format "refs/imerge/%s/state" it))
         it)))

(defun magit-imerge-current-name ()
  "Return the current incremental merge by name.

This name corresponds to the name that would have an asterisk in
the output of `git imerge list'.  In other words, the name that
`git imerge continue' and `git imerge finish' would use by
default.

Note that if there is an active incremental merge, as defined by
`magit-imerge-in-progress-p', this function should return a
non-nil value.  On the other hand, this function may return a
value even when `magit-imerge-in-progress-p' returns nil.

If there are no existing incremental merges, return nil."
  (let ((names (magit-imerge-names)))
    (cond ((null names)
           nil)
          ((= (length names) 1)
           (car names))
          (t
           (magit-imerge--default-name)))))

(defvar magit-imerge--active nil)
(defvar magit-imerge--starting-branch nil
  "Current branch at the time an incremental merge was started.")
(defvar magit-imerge-finish-arguments)

(defun magit-imerge--record-start ()
  "Set the active incremental merge.
Any command that starts a git-imerge sequence should call this
function."
  (setq magit-imerge--active t)
  (setq magit-imerge--starting-branch (magit-get-current-branch))
  (setq magit-imerge-finish-arguments nil))

(defun magit-imerge--record-stop ()
  "Stop the active incremental merge.
Any command that stops a git-imerge sequence should call this
function."
  (setq magit-imerge--active nil)
  (setq magit-imerge--starting-branch nil)
  (setq magit-imerge-finish-arguments nil))

(defun magit-imerge-in-progress-p ()
  "Return non-nil if there is an active incremental merge."
  (and magit-imerge--active
       (magit-imerge-current-name)))

(defun magit-imerge--assert-in-progress ()
  (unless (magit-imerge-in-progress-p)
    (user-error "No incremental merge in progress")))

(defun magit-imerge--region-range ()
  (--when-let (magit-region-values 'commit 'branch)
    (deactivate-mark)
    (concat (car (last it)) "^.." (car it))))

;;; Commands

;;;###autoload
(defun magit-imerge-merge (branch &optional args)
  "Incrementally merge BRANCH into the current branch.
$ git imerge merge [ARGS] BRANCH"
  (interactive
   (list (magit-read-other-branch-or-commit "Merge")
         (magit-imerge-arguments)))
  (magit-imerge--record-start)
  (magit-run-git-sequencer "imerge" "merge" args branch))

;;;###autoload
(defun magit-imerge-rebase (branch &optional args)
  "Incrementally rebase the current branch onto BRANCH.
$ git imerge rebase [ARGS] BRANCH"
  (interactive
   (list (magit-read-other-branch-or-commit "Rebase onto")
         (magit-imerge-arguments)))
  (magit-imerge--record-start)
  (magit-run-git-sequencer "imerge" "rebase" args branch))

;;;###autoload
(defun magit-imerge-revert (commit &optional args)
  "Incrementally revert COMMIT.

If a region selects multiple commits, revert all of them.

$ git imerge revert [ARGS] COMMIT
$ git imerge drop [ARGS] <range>"
  (interactive
   (list (or (magit-imerge--region-range)
             (magit-read-branch-or-commit "Revert commit"))
         (magit-imerge-arguments)))
  (magit-imerge--record-start)
  (magit-run-git-sequencer "imerge" "revert" args commit))

;;;###autoload
(defun magit-imerge-drop (commit &optional args)
  "Incrementally drop COMMIT from the current branch.

If a region selects multiple commits, drop all of them.

$ git imerge drop [ARGS] COMMIT
$ git imerge drop [ARGS] <range>"
  (interactive
   (list (or (magit-imerge--region-range)
             (magit-read-branch-or-commit "Drop commit"))
         (magit-imerge-arguments)))
  (magit-imerge--record-start)
  (magit-run-git-sequencer "imerge" "drop" args commit))

;;;; Sequence commands

;;;###autoload
(defun magit-imerge-resume ()
  "Resume an incremental merge.
This can resume a previous git-imerge sequence that was suspended
with `magit-imerge-suspend'.  More generally, it marks a previous
incremental merge as the active one."
  (interactive)
  (cond ((magit-imerge-in-progress-p)
         (user-error "An incremental merge is already in progress"))
        ((magit-anything-unmerged-p)
         (user-error "Cannot resume with merge conflicts")))
  (let ((names (or (magit-imerge-names)
                   (user-error "No git-imerge refs found"))))
    (if (= (length names) 1)
        (message "Resuming with %s" (car names))
      (let* ((default (magit-imerge--default-name))
             (choice (magit-completing-read "Incremental merge name"
                                            names nil t nil nil
                                            default)))
        (unless (equal choice default)
          (magit-set choice "imerge.default"))))
    (magit-imerge--record-start)
    (magit-imerge-continue)))

(defun magit-imerge-suspend ()
  "Suspend the current incremental merge.
It can be resumed with `magit-imerge-resume'."
  (interactive)
  (magit-imerge--assert-in-progress)
  (if (magit-anything-unmerged-p)
      (user-error "Cannot suspend with merge conflicts")
    (magit-imerge--record-stop)
    (magit-refresh)))

(defun magit-imerge-set-finish-arguments (args)
  "Store ARGS for the next `git imerge finish' call."
  (interactive (list (magit-imerge-finish-arguments)))
  (setq magit-imerge-finish-arguments args)
  (magit-refresh))

(defun magit-imerge-finish (&optional args)
  "Finish the current incremental merge.
$ git imerge finish [ARGS]"
  (interactive (list magit-imerge-finish-arguments))
  (magit-imerge--assert-in-progress)
  (magit-run-git-with-editor "imerge" "finish" args)
  (magit-imerge--record-stop))

(defun magit-imerge-abort ()
  "Abort the current incremental merge.

This aborts any in-progress merge, removes the temporary
git-imerge branches for the current incremental merge, and then
checks out the branch, if any, that was current at the time the
sequence was started.

NOTE: This will delete the information for the current
incremental merge.  Use `magit-imerge-suspend' instead if you
plan to return to this incremental merge later."
  (interactive)
  (magit-imerge--assert-in-progress)
  (when (magit-anything-unmerged-p)
    (magit-merge-abort))
  (magit-run-git "imerge" "remove")
  (when (and magit-imerge--starting-branch
             (magit-rev-verify magit-imerge--starting-branch))
    (magit-checkout magit-imerge--starting-branch))
  (magit-imerge--record-stop))

(defun magit-imerge-continue ()
  "Excecute the next step of the current incremental merge."
  (interactive)
  (magit-imerge--assert-in-progress)
  (if (magit-anything-unstaged-p t)
      (user-error "Cannot continue with unstaged changes")
    (magit-run-git "imerge" "continue" "--no-edit")))

(defun magit-imerge--insert-tip (tip)
  ;; The order of these checks follows the same tag > local branch >
  ;; remote branch precedence that git-imerge gives unqualified
  ;; ambiguous revs.
  (cond ((magit-tag-p tip)
         (magit-insert-section (tag tip)
           (insert (propertize tip 'face 'magit-tag))))
        ((magit-local-branch-p tip)
         (magit-insert-section (branch tip)
           (insert (propertize tip 'face 'magit-branch-local))))
        ((magit-remote-branch-p tip)
         (magit-insert-section (branch tip)
           (insert (propertize tip 'face 'magit-branch-remote))))
        (t
         (--if-let (magit-rev-verify-commit tip)
             (magit-insert-section (commit it)
               (insert (propertize tip 'face 'magit-hash)))
           (error "Tip doesn't name a commit")))))

(defun magit-imerge-insert-status ()
  "Insert information about current incremental merge."
  (when (magit-imerge-in-progress-p)
    (let* ((name (or (magit-imerge-current-name)
                     (error "No name, but in progress?")))
           (state (magit-imerge-state name))
           (finish-value
            (lambda (option)
              (--some
               (and (string-match (format "\\`%s=\\(.+\\)"
                                          (regexp-quote option))
                                  it)
                    (match-string 1 it))
               magit-imerge-finish-arguments))))
      (magit-insert-section (imerge)
        (magit-insert-heading "Incremental merge")
        (magit-insert-section (imerge-info)
          (insert (format "Name:   %s\n" name))
          (magit-insert-heading)
          (insert (format "Goal:   %s\n"
                          (or (--when-let (funcall finish-value "--goal")
                                (propertize
                                 it 'face 'magit-imerge-overriding-value))
                              (cdr (assq 'goal state)))))
          (insert (format "Result: %s\n"
                          (or (--when-let (funcall finish-value "--branch")
                                (propertize
                                 it 'face 'magit-imerge-overriding-value))
                              (cdr (assq 'branch state)))))
          (insert "Tips:   ")
          (magit-imerge--insert-tip (cdr (assq 'tip1 state)))
          (insert ", ")
          (magit-imerge--insert-tip (cdr (assq 'tip2 state)))
          (insert ?\n ?\n))
        (magit-insert-section (imerge-diagram)
          (magit-insert-heading
            (propertize "Diagram\n"
                        'face 'magit-section-secondary-heading))
          (insert
           (with-temp-buffer
             (magit-git-insert "imerge" "diagram" "--no-color" "--commits")
             (re-search-backward "^Key:")
             (delete-region (point) (point-max))
             (buffer-string))))))))

(add-hook 'magit-status-sections-hook #'magit-imerge-insert-status t)

;;; Popup

(defun magit-imerge-read-goal (&rest _ignored)
  "Read a value for git-imerge's `--goal' option."
  (magit-read-char-case "Goal " nil
    (?f "[f]ull" "full")
    (?r "[r]ebase" "rebase")
    (?h "rebase with [h]istory" "rebase-with-history")
    (?m "[m]erge" "merge")
    (?d "[d]rop" "drop")
    (?v "re[v]ert" "revert")))

(magit-define-popup magit-imerge-finish-popup
  "Popup console for git-imerge finish."
  'magit-popups
  :options '((?b "Name of the result" "--branch=")
             (?g "Goal" "--goal=" magit-imerge-read-goal))
  :actions '((?s "Set finish arguments" magit-imerge-set-finish-arguments)))

;;;###autoload (autoload 'magit-imerge-popup "magit-imerge" nil t)
(magit-define-popup magit-imerge-popup
  "Popup console for git-imerge."
  'magit-popups
  :switches '("Switches for merge, rebase, revert, and drop"
              (?m "Manually merge all" "--manual")
              "Switches for revert and drop"
              (?f "Limit to first parents" "--first-parent"))
  :options '((?b "Name of the result" "--branch=")
             (?g "Goal" "--goal=" magit-imerge-read-goal)
             (?n "Name of the imerge" "--name="))
  :actions '((?i "Merge" magit-imerge-merge)
             (?r "Rebase" magit-imerge-rebase)
             (?v "Revert" magit-imerge-revert)
             (?d "Drop" magit-imerge-drop)
             (?R "Resume" magit-imerge-resume))
  :sequence-actions '((?i "Continue" magit-imerge-continue)
                      (?s "Suspend" magit-imerge-suspend)
                      (?f "Finish" magit-imerge-finish)
                      (?F "Set finish options" magit-imerge-finish-popup)
                      (?a "Abort" magit-imerge-abort))
  :sequence-predicate 'magit-imerge-in-progress-p
  :max-action-columns 4)

;;;###autoload
(eval-after-load 'magit
  '(progn
     (magit-define-popup-action 'magit-merge-popup
       ?i "Incremental merge" 'magit-imerge-popup)
     (magit-define-popup-sequence-action 'magit-merge-popup
       ?i "Incremental merge" 'magit-imerge-popup)))

(provide 'magit-imerge)
;;; magit-imerge.el ends here
