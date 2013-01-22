;;; fetchmail-ctl --- Simple code for controlling Fetchmail

;; Copyright (C) 2011 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 29 Sep 2011
;; Version: 1.0
;; Keywords: gnus imap mail message fetchmail
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

;; Unlike fetchmail.el, which does a lot more, this module provides very
;; simple control of Fetchmail and Leafnode's fetchnews behind a 'v' keymap
;; in the Gnus *Group* buffer.

(defgroup fetchmail-ctl nil
  "Simple code for controlling Fetchmail."
  :group 'gnus)

(defvar fetchmail-process nil)

(defun process-running-p (name)
  (catch 'proc-running
    (ignore
     (dolist (proc (process-list))
       (if (string= name (process-name proc))
           (if (eq 'run (process-status proc))
               (throw 'proc-running proc)
             (throw 'proc-running nil)))))))

(defun start-fetchmail (&optional name once &rest extra-args)
  (interactive)
  (let ((procname (or name "*fetchmail*")))
    (unless (process-running-p procname)
      (message "Starting Fetchmail...")
      (let ((buf (get-buffer-create procname))
            (args (copy-list extra-args)))
        (unless once (nconc args '("-d" "900")))
        (setq fetchmail-process
              (apply #'start-process procname buf
                     "/usr/local/bin/fetchmail" "-n" "-N" args)))
      (message "Starting Fetchmail...done"))))

(defun safely-kill-process (name &optional signal verb)
  (let ((proc (process-running-p name)))
    (when proc
      (message "%s process %s..." (or verb "Killing") name)
      (signal-process proc (or signal 'SIGHUP))
      (sit-for 0.5)
      (if (eq 'run (process-status proc))
          (display-buffer (process-buffer proc)))
      (if (null signal)
          (while (eq 'run (process-status proc))
            (sit-for 1)))
      (message "%s process %s...done" (or verb "Killing") name))))

(defun shutdown-fetchmail ()
  (interactive)
  (safely-kill-process "*fetchmail*")
  (safely-kill-process "*fetchmail-lists*")
  ;; (safely-kill-process "*fetchmail-spam*")
  (safely-kill-process "*fetchnews*"))

(defun kick-fetchmail ()
  (interactive)
  (safely-kill-process "*fetchmail*" 'SIGUSR1 "Kicking")
  (safely-kill-process "*fetchmail-lists*" 'SIGUSR1 "Kicking")
  ;; (safely-kill-process "*fetchmail-spam*" 'SIGUSR1 "Kicking")
  )

(defun get-buffer-or-call-func (name func)
  (let ((buf (get-buffer name)))
    (or buf
        (progn
          (save-window-excursion
            (save-excursion
              (funcall func)))
          (get-buffer name)))))

(defun get-buffer-and-call-func (name func)
  (let ((buf (get-buffer name)))
    (if (and buf
             (or (not (get-buffer-process buf))
                 (not (eq 'run (process-status (get-buffer-process buf))))))
        (kill-buffer buf))
    (get-buffer-or-call-func name func)))

(defun switch-to-fetchmail ()
  (interactive)
  (let ((fetchmail-buf
         (get-buffer-or-call-func
          "*fetchmail*"
          (function
           (lambda ()
             (start-fetchmail "*fetchmail*" nil "--idle")))))
        (fetchmail-lists-buf
         (get-buffer-or-call-func
          "*fetchmail-lists*"
          (function
           (lambda ()
             (let ((process-environment (copy-alist process-environment)))
               (setenv "FETCHMAILHOME" (expand-file-name "~/Messages/Newsdir"))
               (start-fetchmail "*fetchmail-lists*" nil
                                "-f" (expand-file-name
                                      "~/Messages/fetchmailrc.lists")))))))
        (fetchmail-spam-buf
         (get-buffer-or-call-func
          "*fetchmail-spam*"
          (function
           (lambda ()
             (let ((process-environment (copy-alist process-environment)))
               (setenv "FETCHMAILHOME" (expand-file-name "~/Messages/Maildir"))
               (start-fetchmail "*fetchmail-spam*" t
                                "-f" (expand-file-name
                                      "~/Messages/fetchmailrc.spam")))))))
        (fetchnews-buf
         (get-buffer-or-call-func
          "*fetchnews*"
          (function
           (lambda ()
             (start-process "*fetchnews*"
                            (get-buffer-create "*fetchnews*")
                            (executable-find "fetchnews")
                            "-F" (expand-file-name "~/Messages/leafnode/config")
                            "-vvv" "-n")))))
        (cur-buf (current-buffer)))
    (delete-other-windows)
    (flet ((switch-in-other-buffer
            (buf)
            (when buf
              (split-window-vertically)
              (balance-windows)
              (switch-to-buffer-other-window buf))))
      (switch-to-buffer cur-buf)
      (switch-in-other-buffer fetchmail-buf)
      (switch-in-other-buffer fetchmail-lists-buf)
      (switch-in-other-buffer fetchmail-spam-buf)
      (switch-in-other-buffer fetchnews-buf)
      (select-window (get-buffer-window cur-buf))
      (balance-windows))))

(add-hook 'gnus-after-exiting-gnus-hook 'shutdown-fetchmail)

(defun fetchnews-post ()
  (interactive)
  (async-shell-command
   (format "fetchnews -F %s -vv -n -P"
           (expand-file-name "~/Messages/leafnode/config"))))

(eval-after-load "gnus-group"
  '(progn
     (define-key gnus-group-mode-map [?v ?b] 'switch-to-fetchmail)
     (define-key gnus-group-mode-map [?v ?o] 'start-fetchmail)
     (define-key gnus-group-mode-map [?v ?d] 'shutdown-fetchmail)
     (define-key gnus-group-mode-map [?v ?k] 'kick-fetchmail)
     (define-key gnus-group-mode-map [?v ?p] 'fetchnews-post)))

(provide 'fetchmail-ctl)

;;; fetchmail-ctl.el ends here
