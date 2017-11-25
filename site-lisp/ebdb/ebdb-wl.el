;;; ebdb-wl.el --- EBDB interface to Wanderlust  -*- lexical-binding: t; -*-

;; Copyright (C) 2017  Free Software Foundation, Inc.

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
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; EBDB's interface to the Wanderlust email client.

;;; Code:

(require 'ebdb-mua)

(autoload 'elmo-message-entity-field "ext:elmo-msgdb")
(autoload 'elmo-message-entity "ext:elmo")
(autoload 'wl-summary-message-number "ext:wl-summary")
(autoload 'wl-summary-set-message-buffer-or-redisplay "ext:wl-summary")

(defvar wl-current-summary-buffer)
(defvar wl-summary-buffer-elmo-folder)
(defvar wl-message-buffer)
(defvar wl-summary-mode-map)
(defvar wl-draft-mode-map)
(defvar wl-folder-buffer-name)
(defvar wl-highlight-signature-separator)

(defgroup ebdb-wl nil
  "Options for EBDB's interaction with Wanderlust."
  :group 'ebdb-mua)

;; This rebinds <TAB> in `wl-draft-mode-map' to `ebdb-complete-mail'.
;; WL has its own completion mechanism that we could hook into, by
;; setting `wl-address-init-function' to our own function that
;; populates `wl-address-completion-list', but that would mean that
;; we're basically duplicating most of the information in the EBDB,
;; and `ebdb-complete-mail' works fine in `wl-draft-mode'.
(defcustom ebdb-wl-use-ebdb-completion nil
  "If non-nil, use EBDB mail completion in WL draft mode."
  :group 'ebdb-wl
  :type 'bool)

(cl-defmethod ebdb-mua-message-header ((header string)
				       &context (major-mode mime-view-mode))
  "Extract a message header in Wanderlust."
  (elmo-message-entity-field
   ;; It's possibly not safe to assume `wl-current-summary-buffer' is live?
   (with-current-buffer wl-current-summary-buffer
     (elmo-message-entity wl-summary-buffer-elmo-folder
			  (wl-summary-message-number)))
   (intern (downcase header)) 'string))

(cl-defmethod ebdb-mua-prepare-article (&context (major-mode wl-summary-mode))
  (wl-summary-set-message-buffer-or-redisplay))

(cl-defmethod ebdb-make-buffer-name (&context (major-mode mime-view-mode))
  (format "*%s-Wl*" ebdb-buffer-name))

(cl-defmethod ebdb-make-buffer-name (&context (major-mode wl-summary-mode))
  (format "*%s-Wl*" ebdb-buffer-name))

(cl-defmethod ebdb-make-buffer-name (&context (major-mode wl-folder-mode))
  (format "*%s-Wl*" ebdb-buffer-name))

(cl-defmethod ebdb-make-buffer-name (&context (major-mode wl-draft-mode))
  (format "*%s-Wl-Draft*" ebdb-buffer-name))

(cl-defmethod ebdb-popup-window (&context (major-mode mime-view-mode))
  (list (get-buffer-window) 0.3))

(defsubst ebdb-wl-goto-signature (&optional beginning)
  "Goto the signature in the current message buffer.
Leaves point at the end (or, with non-nil BEGINNING, the
beginning) of the signature separator."
  (re-search-forward
   (mapconcat
    #'identity
    (cons "\n==+\n" wl-highlight-signature-separator)
    "\\|")
   (point-max) t)
  (when beginning
    (goto-char (match-beginning 0)))
  (point))

(cl-defmethod ebdb-mua-article-body (&context (major-mode wl-summary-mode))
  (with-current-buffer wl-message-buffer
    (when (re-search-forward "^$" (point-max) t)
      (buffer-substring-no-properties
       (point)
       (or (ebdb-wl-goto-signature t)
	   (point-max))))))

(cl-defmethod ebdb-mua-article-signature (&context (major-mode wl-summary-mode))
  (with-current-buffer wl-message-buffer
    (when (re-search-forward "^$" (point-max) t)
      (or (and (ebdb-wl-goto-signature)
	       (buffer-substring-no-properties (point) (point-max)))
	  ""))))

(defun ebdb-wl-quit-window ()
  "Quit EBDB window when quitting WL summary buffer."
  ;; This runs in a hook, which are run in no buffer: we need to be in
  ;; a WL buffer in order to get back the correct EBDB buffer name.
  (with-current-buffer wl-folder-buffer-name
    (let ((win (get-buffer-window (ebdb-make-buffer-name))))
      (when win
	(quit-window nil win)))))

(defun ebdb-insinuate-wl ()
  "Hook EBDB into Wanderlust."
  (define-key wl-summary-mode-map ";" ebdb-mua-keymap)
  (when ebdb-wl-use-ebdb-completion
    (define-key wl-draft-mode-map (kbd "TAB") #'ebdb-complete-mail))
  (add-hook 'wl-summary-exit-hook #'ebdb-wl-quit-window))

(add-hook 'wl-folder-mode-hook #'ebdb-insinuate-wl)

(add-hook 'wl-message-redisplay-hook #'ebdb-mua-auto-update)

(provide 'ebdb-wl)
;;; ebdb-wl.el ends here
