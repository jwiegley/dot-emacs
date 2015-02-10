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
    (action . (("Find File" . helm-c-git-find-file)))
    (candidates-in-buffer)
    (type . file))
  "Search for files in the current Git project.")

(defvar helm-c-source-bash-history
  '((name . "Bash History")
    (candidates . helm-c-bash-history-set-candidates)
    (action . (("Execute Command" . helm-c-bash-history-action)))
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

(defun helm-c-bash-history-set-candidates (&optional request-prefix)
  (let ((pattern (replace-regexp-in-string
                  " " ".*"
                  (or (and request-prefix
                           (concat request-prefix
                                   " " helm-pattern))
                      helm-pattern)))
        (fun (if helm-buffers-fuzzy-matching
                 #'helm--mapconcat-candidate
               #'identity)))
    (with-current-buffer (find-file-noselect "~/.bash_history" t t)
      (auto-revert-mode -1)
      (goto-char (point-max))
      (loop for pos = (re-search-backward (funcall fun pattern) nil t)
            while pos
            collect (replace-regexp-in-string
                     "\\`:.+?;" ""
                     (buffer-substring (line-beginning-position)
                                       (line-end-position)))))))

(defun helm-c-bash-history-action (candidate)
  (async-shell-command candidate))

(defun helm-command-from-bash ()
  (interactive)
  (require 'helm)
  (helm-other-buffer 'helm-c-source-bash-history "*helm bash history*"))

(provide 'helm-commands)

;;; helm-commands.el ends here
