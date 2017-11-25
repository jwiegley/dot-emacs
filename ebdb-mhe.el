;;; ebdb-mhe.el --- EBDB interface to mh-e           -*- lexical-binding: t; -*-

;; Copyright (C) 2016-2017  Free Software Foundation, Inc.

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

;; EBDB interface to mh-e.  This was copied from the file bbdb-mhe.el,
;; written by Todd Kaufman with contributions from Fritz Knabe and
;; Jack Repenning.

;;; Code:

(require 'ebdb-com)
(require 'ebdb-mua)
(require 'mh-e)
(if (fboundp 'mh-version)
    (require 'mh-comp))              ; For mh-e 4.x
(require 'advice)

;; A simplified `mail-fetch-field'.  We could use instead (like rmail):
;; (mail-header (intern-soft (downcase header)) (mail-header-extract))
(defun ebdb/mh-header (header)
  "Find and return the value of HEADER in the current buffer.
Returns the empty string if HEADER is not in the message."
  (let ((case-fold-search t))
    (if mh-show-buffer (set-buffer mh-show-buffer))
    (goto-char (point-min))
    ;; This will be fooled if HEADER appears in the body of the message.
    ;; Also, it fails if HEADER appears more than once.
    (cond ((not (re-search-forward header nil t)) "")
          ((looking-at "[\t ]*$") "")
          (t (re-search-forward "[ \t]*\\([^ \t\n].*\\)$" nil t)
           (let ((start (match-beginning 1)))
             (while (progn (forward-line 1)
                           (looking-at "[ \t]")))
             (backward-char 1)
             (buffer-substring-no-properties start (point)))))))


(cl-defmethod ebdb-make-buffer-name (&context (major-mode mhe-mode))
  "Produce a EBDB buffer name associated with mh-hmode."
  (format "*%s-MHE*" ebdb-buffer-name))

(cl-defmethod ebdb-make-buffer-name (&context (major-mode mhe-summary-mode))
  "Produce a EBDB buffer name associated with mh-hmode."
  (format "*%s-MHE*" ebdb-buffer-name))

(cl-defmethod ebdb-make-buffer-name (&context (major-mode mhe-folder-mode))
  "Produce a EBDB buffer name associated with mh-hmode."
  (format "*%s-MHE*" ebdb-buffer-name))

(cl-defmethod ebdb-mua-message-header ((header string)
				   &context (major-mode mhe-mode))
  (ebdb/mh-header header))

(cl-defmethod ebdb-mua-message-header ((header string)
				   &context (major-mode mhe-summary-mode))
  (ebdb/mh-header header))

(cl-defmethod ebdb-mua-message-header ((header string)
				   &context (major-mode mhe-folder-mode))
  (ebdb/mh-header header))

(cl-defmethod ebdb-mua-prepare-article (&context (major-mode mhe-mode))
  (mh-show))

(cl-defmethod ebdb-mua-prepare-article (&context (major-mode mhe-summary-mode))
  (mh-show))

(cl-defmethod ebdb-mua-prepare-article (&context (major-mode mhe-folder-mode))
  (mh-show))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Use EBDB for interactive spec of MH-E commands

(defadvice mh-send (before mh-ebdb-send act)
  (interactive
   (list (ebdb-completing-read-mails "To: ")
         (ebdb-completing-read-mails "Cc: ")
         (read-string "Subject: "))))

(defadvice mh-send-other-window (before mh-ebdb-send-other act)
  (interactive
   (list (ebdb-completing-read-mails "To: ")
         (ebdb-completing-read-mails "Cc: ")
         (read-string "Subject: "))))

(defadvice mh-forward (before mh-ebdb-forward act)
  (interactive
   (list (ebdb-completing-read-mails "To: ")
         (ebdb-completing-read-mails "Cc: ")
         (if current-prefix-arg
             (mh-read-seq-default "Forward" t)
           (mh-get-msg-num t)))))

(defadvice mh-redistribute (before mh-ebdb-redist act)
  (interactive
   (list (ebdb-completing-read-mails "Redist-To: ")
         (ebdb-completing-read-mails "Redist-Cc: ")
         (mh-get-msg-num t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun ebdb-insinuate-mh ()
  "Hook EBDB into MH-E."
  (define-key mh-folder-mode-map ";" ebdb-mua-keymap)
  (when ebdb-complete-mail
      (define-key mh-letter-mode-map "\M-;" 'ebdb-complete-mail)
      (define-key mh-letter-mode-map "\e\t" 'ebdb-complete-mail)))

(add-hook 'mh-show-hook 'ebdb-mua-auto-update)

(add-hook 'mh-folder-mode-hook 'ebdb-insinuate-mh)

(provide 'ebdb-mhe)
;;; ebdb-mhe.el ends here
