;;; mc-move.el --- Functions to move cursors in multiple-cursors mode.

;; Copyright (c) 2013-2017 Akinori MUSHA
;;
;; All rights reserved.
;;
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions
;; are met:
;; 1. Redistributions of source code must retain the above copyright
;;    notice, this list of conditions and the following disclaimer.
;; 2. Redistributions in binary form must reproduce the above copyright
;;    notice, this list of conditions and the following disclaimer in the
;;    documentation and/or other materials provided with the distribution.
;;
;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
;; ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
;; IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;; ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
;; FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
;; DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
;; OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
;; HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
;; LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
;; OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
;; SUCH DAMAGE.

;; Author: Akinori MUSHA <knu@iDaemons.org>
;; URL: https://github.com/knu/mc-extras.el
;; Created: 16 Aug 2013
;; Package-Requires: ((multiple-cursors "1.2.1"))
;; Keywords: editing, cursors

;;; Commentary:
;;
;; This library contains functions to move cursors in multiple-cursors
;; mode.
;;
;; Suggested key bindings are as follows:
;;
;;   (define-key mc/keymap (kbd "C-. .") 'mc/move-to-column)
;;   (define-key mc/keymap (kbd "C-. =") 'mc/compare-chars)

;;; Code:

(require 'cl)
(require 'multiple-cursors-core)

;;;###autoload
(defun mc/move-to-column (column)
  "Move every cursor to column COLUMN.
If COLUMN is omitted, move every fake cursor to the same column as the real cursor."
  (interactive "P")
  (let ((current-prefix-arg (if column (prefix-numeric-value column) (current-column))))
    (mc/execute-command-for-all-cursors 'move-to-column)))

(add-to-list 'mc--default-cmds-to-run-once 'mc/move-to-column)

;;;###autoload
(defun mc/compare-chars (&optional arg)
  "Compare the character at point with that at each fake cursor, and move forward as far as they all match.
With an optional argument, move backwards by calling `mc/compare-chars-backward'.
This command pushes the mark before moving cursors."
  (interactive "P")
  (if arg (mc/compare-chars-backward)
    (mc/compare-chars-forward)))

(add-to-list 'mc--default-cmds-to-run-once 'mc/compare-chars)

;;;###autoload
(defun mc/compare-chars-forward ()
  "Compare the character at point with that at each fake cursor, and move forward as far as they all match.
This command pushes the mark before moving cursors."
  (interactive)
  (let (current-prefix-arg)
    (mc/execute-command-for-all-cursors 'push-mark-command)
    (while (loop for cursor in (mc/all-fake-cursors)
                 with c = (following-char)
                 always (char-equal (char-after (overlay-start cursor)) c))
      (mc/execute-command-for-all-cursors 'forward-char))))

(add-to-list 'mc--default-cmds-to-run-once 'mc/compare-chars-forward)

;;;###autoload
(defun mc/compare-chars-backward ()
  "Backwards version of `mc/compare-chars-forward'."
  (interactive)
  (let (current-prefix-arg)
    (mc/execute-command-for-all-cursors 'push-mark-command)
    (while (loop for cursor in (mc/all-fake-cursors)
                 with c = (preceding-char)
                 always (char-equal (char-before (overlay-start cursor)) c))
      (mc/execute-command-for-all-cursors 'backward-char))))

(add-to-list 'mc--default-cmds-to-run-once 'mc/compare-chars-backward)

(provide 'mc-move)

;;; mc-move.el ends here
