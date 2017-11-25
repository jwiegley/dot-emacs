;;; ebdb-message.el --- EBDB interface to mail composition packages  -*- lexical-binding: t; -*-

;; Copyright (C) 2016-2017  Free Software Foundation, Inc.

;; Author: Eric Abrahamsen <eric@ericabrahamsen.net>

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

;; Code for interaction with message composition and sending packages.

;;; Code:


(require 'ebdb-mua)
(require 'message)
(require 'sendmail)

(defvar gnus-window-to-buffer)

(defgroup ebdb-mua-message nil
  "Message-specific EBDB customizations"
  :group 'ebdb-mua)
(put 'ebdb-mua-message 'custom-loads '(ebdb-message))

;; Suggestions welcome: What are good keybindings for the following
;; commands that do not collide with existing bindings?
;; (define-key message-mode-map "'" 'ebdb-mua-display-recipients)
;; (define-key message-mode-map ";" 'ebdb-mua-edit-field-recipients)
;; (define-key message-mode-map "/" 'ebdb)

(defsubst ebdb-message-buffer-name ()
  (format "*%s-Message*" ebdb-buffer-name))

(cl-defmethod ebdb-make-buffer-name (&context (major-mode message-mode))
  "Produce a EBDB buffer name associated with Message mode."
  (ebdb-message-buffer-name))

(cl-defmethod ebdb-make-buffer-name (&context (major-mode mail-mode))
  "Produce a EBDB buffer name associated with Mail mode."
  (ebdb-message-buffer-name))

(cl-defmethod ebdb-mua-message-header ((header string)
				    &context (major-mode message-mode))
  (message-field-value header))

(cl-defmethod ebdb-mua-message-header ((header string)
				    &context (major-mode notmuch-message-mode))
  (message-field-value header))

(cl-defmethod ebdb-mua-message-header ((header string)
				    &context (major-mode mail-mode))
  (message-field-value header))

(cl-defmethod ebdb-popup-window (&context (major-mode message-mode))
  (list (get-buffer-window) 0.4))

(cl-defmethod ebdb-popup-window (&context (major-mode mail-mode))
  (list (get-buffer-window) 0.4))

(defun ebdb-insinuate-message ()
  ;; We don't currently bind the `ebdb-mua-keymap'.
  (when ebdb-complete-mail
    (cl-pushnew '("^\\(Resent-\\)?\\(To\\|B?Cc\\|Reply-To\\|From\\|Mail-Followup-To\\|Mail-Copies-To\\):" . ebdb-complete-mail)
		message-completion-alist
		:test #'equal)
    (define-key message-mode-map (kbd "TAB") 'ebdb-complete-mail))
  ;; Other MUAs clear the EBDB buffer before displaying (in
  ;; `ebdb-mua-auto-update', the call to `ebdb-display-records' does
  ;; not pass the "append" flag).  Displaying in message-mode does
  ;; pass the "append" flag (in `ebdb-complete-mail-cleanup'), so we
  ;; do the undisplay manually.
  (ebdb-undisplay-records))

(defun ebdb-insinuate-mail ()
  "Hook EBDB into Mail Mode."
  ;; We don't currently bind the `ebdb-mua-keymap'.
  (if ebdb-complete-mail
      (define-key mail-mode-map "\M-\t" 'ebdb-complete-mail))
  (ebdb-undisplay-records))

(add-hook 'message-mode-hook 'ebdb-insinuate-message)
(add-hook 'mail-setup-hook 'ebdb-insinuate-mail)
(add-hook 'message-send-hook 'ebdb-mua-auto-update)
(add-hook 'mail-send-hook 'ebdb-mua-auto-update)

;; Slightly convoluted, but does it the "right way".  The
;; `message-header-setup-hook' creates and populates the
;; *EBDB-Message* buffer after the message-mode buffer is created.
;; The gnus window configuration stanza makes sure it's displayed
;; after the message buffer is set up.
(with-eval-after-load 'gnus-win
  (add-to-list 'gnus-window-to-buffer `(ebdb . ,(ebdb-message-buffer-name)))
  (add-hook 'message-header-setup-hook 'ebdb-mua-auto-update)

  (gnus-add-configuration
   '(reply
     (horizontal 1.0
		 (message 1.0 point)
		 (ebdb 0.4))))

  (gnus-add-configuration
   '(reply-yank
     (horizontal 1.0
		 (message 1.0 point)
		 (ebdb 0.4)))))

(provide 'ebdb-message)
;;; ebdb-message.el ends here
