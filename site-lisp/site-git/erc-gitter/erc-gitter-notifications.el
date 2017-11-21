;;; erc-gitter-notifications.el --- Gitter-Notifications module  -*- lexical-binding: t; -*-

;; Copyright (C) 2014

;; Author:  Jonathan Leech-Pepin <jonathan.leechpepin AT gmail.com>
;; Keywords: tools, extension

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

(require 'erc)
(require 'erc-button)

;;;; Variables

;;;;; Customizable

(defcustom erc-gitter-bot-handling 't
  "How to handle messages from gitter integration.

'buffer will send messages to a separate buffer
nil will do nothing with it.
non-nil values will set `gitter' as a fool."
  :type '(choice (const :tag "Do nothing" nil)
                 (const :tag "Separate buffer" 'buffer)
                 (symbol :tag "Treat as Fool" 't))
  :group 'erc-gitter)

(defface erc-gn-notifications-face
  '((t :inherit erc-current-nick-face))
  ""
  :group 'erc-gitter-faces)

;;;;; Internal

(defvar erc-gn-pending 0
  "How many notifications are pending in the \"*Gitter
  Notifications*\" buffer.")

(defvar erc-gn-unread-overlay nil
  "Overlay variable for unread notifications")
;;;; Gitter-bot notification handling

(defun erc-gitter-gitter-is-fool ()
  "Add the gitter-bot to the list of fools.

It will be treated as any other fool."
  (interactive)
  (add-to-list 'erc-fools "gitter!gitter@gitter.im"))

(defun erc-gitter-gitter-is-no-fool ()
  "Remove the gitter-bot from the list of fools."
  (interactive)
  (setq erc-fools (delete "gitter!gitter@gitter.im" erc-fools)))

;;;; Gitter Notifications Buffer

(defun erc-gitter-bot-to-buffer (match-type nickuserhost message)
  (when (and (eq match-type 'fool)
             (string= "gitter!gitter@gitter.im" nickuserhost))
    (let* ((buf (erc-gn-make-buffer))
           (len (- (length message) 2))
           (cb (get-text-property len 'erc-callback message))
           (data (get-text-property len 'erc-data message)))
      (with-current-buffer buf
        (save-excursion
          (let ((end (point-max)))
          (goto-char end)
          (insert message)
          (put-text-property end (point) 'erc-data data)
          (put-text-property end (point) 'erc-callback cb))))
      (erc-gn-update)
      (erc-hide-fools match-type nickuserhost message))))

(defun erc-gn-make-buffer ()
  (when (eq erc-gitter-bot-handling 'buffer)
    (unless (get-buffer "*Gitter Notifications*")
      (let ((buf (get-buffer-create "*Gitter Notifications*")))
        (with-current-buffer buf
          (gitter-notifications-mode)
          (unless erc-gn-unread-overlay
            (let ((over (make-overlay (point-min) (point-max)
                                      (current-buffer) nil t)))
              (overlay-put over 'face
                           '(t :inherit header-line :box nil))
              (setq erc-gn-unread-overlay over))))))
    (get-buffer "*Gitter Notifications*")))

(defvar gitter-notifications-mode-map
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map special-mode-map)
    (define-key map "g" nil) ; nothing to revert
    (define-key map "q" #'bury-buffer)
    ;; (define-key map (kbd "<return>") #'erc-gn-visit)
    (define-key map "p" #'erc-gn-previous)
    (define-key map "n" #'erc-gn-next)
    (define-key map [remap next-line] #'erc-gn-next)
    (define-key map [remap previous-line] #'erc-gn-previous)
    (define-key map (kbd "<return>") #'erc-button-press-button)
    map))

(define-derived-mode gitter-notifications-mode special-mode
  "Gitter-Notifications"
  "Major mode used in the \"*Gitter Notifications*\" buffer."
  :group 'erc-gitter)

(defun erc-gn-switch-to-notif ()
  (interactive)
    (if (eq erc-gitter-bot-handling 'buffer)
        (progn
          (switch-to-buffer (erc-gn-make-buffer))
          (when erc-gn-pending
            (goto-char (overlay-start erc-gn-unread-overlay)))
          (erc-gn-update 0))
      (user-error "Gitter notifications are not being tracked.")))

(defun erc-gn-next ()
  (interactive)
  ;; Test if current notification is unread, if so mark unread when
  ;; moving.
  (let ((unread (>= (point) (overlay-start erc-gn-unread-overlay))))
    (condition-case nil
        (progn
          (forward-char 1)
          (re-search-forward "^\\[.*?\\]" nil)
          (beginning-of-line 1)
          (when unread
            (move-overlay erc-gn-unread-overlay (point)
                          (overlay-end erc-gn-unread-overlay))))
      (error (and (move-overlay erc-gn-unread-overlay (point-max)
                                (point-max))
                  (beginning-of-line 1)))))
  (erc-gn-update 0))

(defun erc-gn-previous ()
  (interactive)
  (re-search-backward "^\\[.*?\\]" nil 'noerror)
  (erc-gn-update 0))

;;;; Gitter Notification Mode-Line

(defvar gitter-notifications-mode-line-map
  (let ((map (make-sparse-keymap)))
    (define-key map [mode-line mouse-1] #'erc-gn-switch-to-notif)
    (define-key map [mode-line mouse-3] #'erc-gn-clear-notif)
    map))

(defun erc-gn-notifications ()
  (setq erc-gn-notifications
        (if (> erc-gn-pending 0)
            (list "["
                  `(:propertize
                    (:eval (format "G:%d" erc-gn-pending))
                    help-echo
                    (format "%d notifications pending from Gitter\n\
mouse-1: Display \"*Gitter Notifications*\" buffer\n\
mouse-3: Clear pending notifications"
                            erc-gn-pending)
                    local-map ,gitter-notifications-mode-line-map
                    face erc-gn-notifications-face)
                  "]")
          "")))

(defvar erc-gn-notifications nil
  "Gitter Notification string for modeline.")
(put 'erc-gn-notifications 'risky-local-variable t)

(defun erc-gn-update (&optional count)
  (if count
      (setq erc-gn-pending count)
    (setq erc-gn-pending (1+ erc-gn-pending)))
  (erc-gn-notifications))

(defun erc-gn-clear-notif ()
  (interactive)
  (move-overlay erc-gn-unread-overlay (point-min) (point-max))
  (erc-gn-update 0))

(provide 'erc-gitter-notifications)
;;; erc-gitter-notifications.el ends here
