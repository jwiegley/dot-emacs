;;; circe-chanop.el --- Provide common channel operator commands

;; Copyright (C) 2006, 2015  Jorgen Schaefer

;; Author: Jorgen Schaefer <forcer@forcix.cx>

;; This file is part of Circe.

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 3
;; of the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
;; 02110-1301  USA

;;; Commentary:

;; This Circe module provides some often-used chanop commands. I was
;; very reluctant to add this. None of these commands will make it in
;; the core, or even be provided by default. You should have to go to
;; great lengths to use them.

;; Always remember the Tao of IRC:
;;
;;     IGNORE is the weapon of an IRC knight. Not as clumsy or as
;;     random as a kickban.

;;; Code:

(require 'circe)

(defun circe-command-MODE (mode)
  "Set MODE in the current channel."
  (interactive "sMode change: ")
  (cond
   ((not (string-match "^[+-]" mode))
    (irc-send-raw (circe-server-process)
                  (format "MODE %s" mode)))
   ((eq major-mode 'circe-channel-mode)
    (irc-send-raw (circe-server-process)
                  (format "MODE %s %s" circe-chat-target mode)))
   (t
    (circe-display-server-message "Not in a channel buffer."))))

(defun circe-command-BANS (&optional ignored)
  "Show channel bans"
  (if (not circe-chat-target)
      (circe-display-server-message "No target for current buffer")
    (irc-send-raw (circe-server-process)
                  (format "MODE %s +b" circe-chat-target))))

(defun circe-command-KICK (nick &optional reason)
  "Kick WHO from the current channel with optional REASON."
  (interactive "sKick who: \nsWhy: ")
  (if (not (eq major-mode 'circe-channel-mode))
      (circe-display-server-message "Not in a channel buffer.")
    (when (not reason)
      (if (string-match "^\\([^ ]*\\) +\\(.+\\)" nick)
          (setq reason (match-string 2 nick)
                nick (match-string 1 nick))
        (setq reason "-")))
    (irc-send-raw (circe-server-process)
                  (format "KICK %s %s :%s"
                          circe-chat-target nick reason))))

(defun circe-command-GETOP (&optional ignored)
  "Ask chanserv for op on the current channel."
  (interactive)
  (if (not (eq major-mode 'circe-channel-mode))
      (circe-display-server-message "Not in a channel buffer.")
    (irc-send-PRIVMSG (circe-server-process)
                      "chanserv"
                      (format "op %s" circe-chat-target))))

(defun circe-command-DROPOP (&optional ignored)
  "Lose op mode on the current channel."
  (interactive)
  (if (not (eq major-mode 'circe-channel-mode))
      (circe-display-server-message "Not in a channel buffer.")
    (irc-send-raw (circe-server-process)
                  (format "MODE %s -o %s"
                          circe-chat-target
                          (circe-nick)))))

;; For KICKBAN (requested by Riastradh), we'd need a callback on a
;; USERHOST command.

(provide 'circe-chanop)
;;; circe-chanop.el ends here
