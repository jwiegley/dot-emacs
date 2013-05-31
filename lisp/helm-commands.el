;;; helm-commands --- More helm commands that I use

;; Copyright (C) 2012 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 03 Jul 2012
;; Version: 1.0
;; Keywords: helm
;; X-URL: https://github.com/jwiegley/dot-emacs

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

;; 

(defgroup helm-commands nil
  "More helm commands that I use"
  :group 'helm)

(defvar helm-c-source-git-files
  '((name . "Files under Git version control")
    (init . helm-c-source-git-files-init)
    (action . (("Execute Command" . find-file)))
    (candidates-in-buffer)
    (type . file))
  "Search for files in the current Git project.")

(defvar helm-c-source-zsh-history
  '((name . "Zsh History")
    (candidates . helm-c-zsh-history-set-candidates)
    (action . (("Execute Command" . helm-c-zsh-history-action)))
    (volatile)
    (requires-pattern . 3)
    (delayed)))

(defun my-helm-apropos ()
  (interactive)
  (require 'helm-elisp)
  (require 'helm-misc)
  (let ((default (thing-at-point 'symbol)))
    (helm
     :prompt "Info about: "
     :candidate-number-limit 15
     :sources
     (append (mapcar (lambda (func)
                       (funcall func default))
                     '(helm-c-source-emacs-commands
                       helm-c-source-emacs-functions
                       helm-c-source-emacs-variables
                       helm-c-source-emacs-faces
                       helm-c-source-helm-attributes))
             '(helm-c-source-info-emacs
               helm-c-source-info-elisp
               helm-c-source-info-gnus
               helm-c-source-info-org
               helm-c-source-info-cl
               helm-c-source-emacs-source-defun)))))

(defun helm-c-zsh-history-set-candidates (&optional request-prefix)
  (let ((pattern (replace-regexp-in-string
                  " " ".*"
                  (or (and request-prefix
                           (concat request-prefix
                                   " " helm-pattern))
                      helm-pattern))))
    (with-current-buffer (find-file-noselect "~/.zsh_history" t t)
      (auto-revert-mode -1)
      (goto-char (point-max))
      (loop for pos = (re-search-backward pattern nil t)
            while pos
            collect (replace-regexp-in-string
                     "\\`:.+?;" ""
                     (buffer-substring (line-beginning-position)
                                       (line-end-position)))))))

(defun helm-c-zsh-history-action (candidate)
  (async-shell-command candidate))

(defun helm-command-from-zsh ()
  (interactive)
  (require 'helm)
  (helm-other-buffer 'helm-c-source-zsh-history "*helm zsh history*"))

(defun helm-c-source-git-files-init ()
  "Build `helm-candidate-buffer' of Git files."
  (let ((dir (substring
              (shell-command-to-string "git rev-parse --git-dir") 0 -1)))
    (with-current-buffer (helm-candidate-buffer 'local)
      (mapcar
       (lambda (item)
         (insert (expand-file-name item (file-name-directory dir)) ?\n))
       (split-string (shell-command-to-string
                      (format "git --git-dir=\"%s\" ls-files" dir)) "\n")))))

(defun helm-find-git-file ()
  (interactive)
  (helm :sources 'helm-c-source-git-files
        :input ""
        :prompt "Find file: "
        :buffer "*Helm git file*"))

(provide 'helm-commands)

;;; helm-commands.el ends here
