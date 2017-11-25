;;; springboard.el --- Temporarily change default-directory for one command

;; Copyright (C) 2012 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 13 Jun 2012
;; Version: 1.0
;; Keywords: helm
;; Package-Requires: ((helm "1.6.9"))
;; X-URL: https://github.com/jwiegley/springboard

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; How many times have you wanted to fire off a quick command, such as M-!,
;; but the directory you want to run the command in isn't the same as the
;; directory of the current buffer?  In those situations, you want a quick way
;; to change the default-directory *for only the next command*.  That is what
;; Springboard aims to solve.
;;
;; Bind it to a convenient key, like Control-., and after you press it you'll
;; see a handy Helm buffer showing the directories of all the files you've
;; recently visited, plus the permanent directory list from
;; `springboard-directories' -- a good place to list your active project
;; directories.
;;
;; Type a few chars to narrow down to the directory of interest, then just
;; type your command, like M-!, C-x C-f, or whatever custom bindings you may
;; have to run PCVS, Magit, etc.  The moment you type your command,
;; Springboard disappears, and if your command needs minibuffer input, you'll
;; now be in the minibuffer for that new command.

;;; Code:

(require 'helm)
(require 'recentf)
(require 'dired)

(defgroup springboard nil
  "Temporarily change default-directory for one command"
  :group 'helm)

(defcustom springboard-directories '("/usr/local")
  "List of directories that are always displayed in the Springboard."
  :type '(repeat directory)
  :group 'springboard)

(defvar springboard-map nil)

;;;###autoload
(defun springboard-apply-passthrough-keys ()
  (setq springboard-map (copy-keymap helm-map))
  (mapc #'(lambda (key) (define-key springboard-map key nil))
        springboard-passthrough-keys))

(defcustom springboard-passthrough-keys '([(control ?x)] [open])
  "List of directories that are always displayed in the Springboard.
If you change this variable outside of the Customization interface,
you must then call `springboard-apply-passthrough-keys'."
  :set #'(lambda (var value)
           (set var value)
           (springboard-apply-passthrough-keys))
  :type '(repeat (sexp :tag "Key Codes"))
  :group 'springboard)

(defcustom springboard-ignored-commands '(self-insert-command
                                          delete-backward-char
                                          abort-recursive-edit)
  "Commands that will not be trapped by Springboard.
If you enter a command in Springboard that you were expecting
Helm to handle, but instead your Springboard buffer suddenly
disappears, then you need to add that command to this list."
  :type '(repeat command)
  :group 'springboard)

(defcustom springboard-recentf-cutoff 50
  "Only consider this many files from the `recentf-files' list."
  :type 'integer
  :group 'springboard)

(defcustom springboard-recentf-filter-function
  (function (lambda (elem) (not (string-match "\\.el\\.gz" elem))))
  "Only use `recentf-files' entries for which function returns non-nil."
  :type 'function
  :group 'springboard)

(defvar springboard-history nil)

(eval-when-compile
  (defvar springboard-trapped nil)
  (defvar springboard-already-trapped nil))

(defun springboard-add-trap ()
  (add-hook 'pre-command-hook 'springboard-trap-command t t))

(defun springboard-remove-trap ()
  (remove-hook 'pre-command-hook 'springboard-trap-command t))

(defun springboard-trap-command ()
  (unless springboard-already-trapped
    (condition-case err
        (if (or (memq this-command springboard-ignored-commands)
                (where-is-internal this-command (list springboard-map) t))
            (setq springboard-trapped nil)
          (message "Trapped command: %s" this-command)
          (setq springboard-trapped t
                springboard-already-trapped t)
          (mapc #'(lambda (buf)
                    (if (minibufferp buf)
                        (with-current-buffer buf
                          (springboard-remove-trap))))
                (buffer-list))
          (helm-confirm-and-exit-minibuffer))
      (error
       (message "Error occurred: %s" err)))))

(defun springboard-current-history ()
  (let ((recentf-filtered-list
         (delete
          nil
          (mapcar (function
                   (lambda (elem)
                     (and (funcall springboard-recentf-filter-function
                                   elem)
                          elem)))
                  recentf-list))))
    (delete-dups
     (append (delete
              nil (mapcar #'(lambda (buf)
                              (let ((path (buffer-file-name buf)))
                                (when path
                                  (if (file-directory-p path)
                                      path
                                    (file-name-directory path)))))
                          (buffer-list)))
             (mapcar #'file-name-directory
                     (butlast recentf-filtered-list
                              (- (length recentf-filtered-list)
                                 springboard-recentf-cutoff)))))))

;;;###autoload
(defun springboard ()
  "`helm'-based command for temporarily changing the default directory."
  (interactive)
  (add-hook 'minibuffer-setup-hook 'springboard-add-trap)
  (add-hook 'minibuffer-exit-hook 'springboard-remove-trap)
  (unwind-protect
      (let* (springboard-trapped
             springboard-already-trapped
             special-display-buffer-names
             special-display-regexps
             helm-persistent-action-use-special-display
             (default-directory
               (helm-comp-read
                "Springboard: " springboard-directories
                :test #'file-directory-p
                :buffer "*Springboard*"
                :history (springboard-current-history)
                :input-history 'springboard-history
                :keymap springboard-map
                :persistent-action #'dired)))
        (message "Directory: %s; Trapped: %s" default-directory
                 springboard-trapped)
        (if springboard-trapped
            (call-interactively this-command)
          (dired default-directory)))
    (remove-hook 'minibuffer-setup-hook 'springboard-add-trap)
    (remove-hook 'minibuffer-exit-hook 'springboard-remove-trap)))

(provide 'springboard)

;;; springboard.el ends here
