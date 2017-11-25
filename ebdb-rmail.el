;;; ebdb-rmail.el --- EBDB interface to Rmail        -*- lexical-binding: t; -*-

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

;; EBDB's interaction with the Rmail MUA.

;;; Code:

(require 'ebdb-com)
(require 'ebdb-mua)
(require 'rmail)
(require 'rmailsum)
(require 'mailheader)

(defun ebdb/rmail-new-flag ()
  "Returns t if the current message in buffer BUF is new."
  (rmail-message-labels-p rmail-current-message ", ?\\(unseen\\),"))

(defun ebdb/rmail-header (header)
  "Pull HEADER out of Rmail header."
  (with-current-buffer rmail-buffer
    (if (fboundp 'rmail-get-header)  ; Emacs 23
        (rmail-get-header header)
      (save-restriction
        (with-no-warnings (rmail-narrow-to-non-pruned-header))
        (mail-header (intern-soft (downcase header))
                     (mail-header-extract))))))

(cl-defmethod ebdb-mua-message-header ((header string)
				   &context (major-mode rmail-mode))
  (ebdb/rmail-header header))

(cl-defmethod ebdb-mua-message-header ((header string)
				   &context (major-mode rmail-summary-mode))
  (ebdb/rmail-header header))

(cl-defmethod ebdb-make-buffer-name (&context (major-mode rmail-mode))
  (format "*%s-Rmail*" ebdb-buffer-name))

(cl-defmethod ebdb-make-buffer-name (&context (major-mode rmail-summary-mode))
  (format "*%s-Rmail*" ebdb-buffer-name))

(defun ebdb-insinuate-rmail ()
  "Hook EBDB into RMAIL."
  (define-key rmail-mode-map ";" ebdb-mua-keymap))

(add-hook 'rmail-mode-hook 'ebdb-insinuate-rmail)

(add-hook 'rmail-show-message-hook 'ebdb-mua-auto-update)

(provide 'ebdb-rmail)
;;; ebdb-rmail.el ends here
