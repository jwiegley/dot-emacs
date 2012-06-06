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

(defun start-fetchmail ()
  (interactive)
  (unless (process-running-p "*fetchmail*")
    (message "Starting Fetchmail...")
    (let ((buf (get-buffer-create "*fetchmail*")))
      (setq fetchmail-process
            (start-process "*fetchmail*" buf
                           "/opt/local/bin/fetchmail" "-d" "900" "-N")))
    (message "Starting Fetchmail...done")))

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
  (safely-kill-process "*fetchmail*"))

(defun kick-fetchmail ()
  (interactive)
  (safely-kill-process "*fetchmail*" 'SIGUSR1 "Kicking"))

(defun switch-to-fetchmail ()
  (interactive)
  (let ((buf (get-buffer "*fetchmail*")))
    (unless buf
      (start-fetchmail)
      (setq buf (get-buffer "*fetchmail*")))
    (display-buffer buf)))

;; (add-hook 'gnus-agent-plugged-hook 'start-fetchmail)
;; (add-hook 'gnus-agent-unplugged-hook 'shutdown-fetchmail)
(add-hook 'gnus-after-exiting-gnus-hook 'shutdown-fetchmail)

(defun fetchnews-fetch ()
  (interactive)
  (if t
      (async-shell-command "fetchmail -f ~/Messages/fetchmailrc.news")
    (async-shell-command "fetchnews -vv -n")))

(defun fetchnews-post ()
  (interactive)
  (async-shell-command "fetchnews -vv -n -P"))

(eval-after-load "gnus-group"
  '(progn
     (define-key gnus-group-mode-map [?v ?b] 'switch-to-fetchmail)
     (define-key gnus-group-mode-map [?v ?o] 'start-fetchmail)
     (define-key gnus-group-mode-map [?v ?d] 'shutdown-fetchmail)
     (define-key gnus-group-mode-map [?v ?g] 'kick-fetchmail)
     (define-key gnus-group-mode-map [?v ?k] 'kick-fetchmail)

     (define-key gnus-group-mode-map [?v ?f] 'fetchnews-fetch)
     (define-key gnus-group-mode-map [?v ?p] 'fetchnews-post)))

(provide 'fetchmail-ctl)

;;; fetchmail-ctl.el ends here
