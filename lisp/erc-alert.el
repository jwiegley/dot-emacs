;;; erc-alert --- Alert me using alert.el for important ERC messages

;; Copyright (C) 2011 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 20 Sep 2011
;; Version: 1.0
;; Keywords: erc alert irc
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

;; Notify me using alert.el when people talk to me in ERC.

(require 'erc)
(require 'alert)

(defgroup erc-alert nil
  "Alert me using alert.el for important ERC messages"
  :group 'erc)

(defcustom erc-priority-people-regexp ".*"
  "Regexp that matches BitlBee users you want active notification for."
  :type 'regexp
  :group 'erc-alert)

(defcustom erc-growl-noise-regexp
  "\\(Logging in:\\|Signing off\\|You're now away\\|Welcome back\\|Setting automatically away\\)"
  "This regexp matches unwanted noise."
  :type 'regexp
  :group 'erc-alert)

;; Unless the user has recently typed in the ERC buffer, highlight the fringe
(alert-add-rule :status   '(buried visible idle)
                :severity '(moderate high urgent)
                :mode     'erc-mode
                :predicate
                #'(lambda (info)
                    (string-match (concat "\\`[^&]" erc-priority-people-regexp
                                          "@BitlBee\\'")
                                  (erc-format-target-and/or-network)))
                :persistent
                #'(lambda (info)
                    ;; If the buffer is buried, or the user has been idle for
                    ;; `alert-reveal-idle-time' seconds, make this alert
                    ;; persistent.  Normally, alerts become persistent after
                    ;; `alert-persist-idle-time' seconds.
                    (memq (plist-get info :status) '(buried idle)))
                :style 'fringe
                :continue t)

(defun erc-alert-important-p (info)
  (let ((message (plist-get info :message))
        (erc-message (plist-get info :data)))
    (and erc-message
         (not (or (string-match "^\\** *Users on #" message)
                  (string-match erc-growl-noise-regexp
                                message))))))

;; If the ERC buffer is not visible, tell the user through Growl
(alert-add-rule :status 'buried
                :mode   'erc-mode
                :predicate #'erc-alert-important-p
                :style 'growl
                :append t)

(alert-add-rule :mode 'erc-mode
                :predicate #'erc-alert-important-p
                :style 'log
                :append t)

(alert-add-rule :mode 'erc-mode :style 'ignore :append t)

(defun my-erc-hook (&optional match-type nick message)
  "Shows a growl notification, when user's nick was mentioned.
If the buffer is currently not visible, makes it sticky."
  (if (or (null match-type) (not (eq match-type 'fool)))
      (let (alert-log-messages)
        (alert (or message (buffer-string)) :severity 'high
               :title (concat "ERC: " (or nick (buffer-name)))
               :data message))))

(add-hook 'erc-text-matched-hook 'my-erc-hook)
(add-hook 'erc-insert-modify-hook 'my-erc-hook)

(provide 'erc-alert)

;;; erc-alert.el ends here
