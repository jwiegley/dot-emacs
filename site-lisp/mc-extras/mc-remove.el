;;; mc-remove.el --- Functions to remove cursors in multiple-cursors mode.

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
;; Created: 12 Jul 2013
;; Package-Requires: ((multiple-cursors "1.2.1"))
;; Keywords: editing, cursors

;;; Commentary:
;;
;; This library contains functions to remove cursors in
;; multiple-cursors mode.
;;
;; Suggested key bindings are as follows:
;;
;;   (define-key mc/keymap (kbd "C-. C-d") 'mc/remove-current-cursor)
;;   (define-key mc/keymap (kbd "C-. C-k") 'mc/remove-cursors-at-eol)
;;   (define-key mc/keymap (kbd "C-. d")   'mc/remove-duplicated-cursors)

;;; Code:

(require 'cl)
(require 'multiple-cursors-core)

;;;###autoload
(defun mc/remove-current-cursor ()
  "Remove the current cursor by replacing the next fake cursor with the real cursor."
  (interactive)
  (let ((next-cursor
         (or (mc/next-fake-cursor-after-point)
             (mc/prev-fake-cursor-before-point)
             (error "This is the only cursor."))))
    (mapc 'mc/remove-fake-cursor
          (remove-if-not 'mc/fake-cursor-p
                         (overlays-at (point))))
    (mc/pop-state-from-overlay next-cursor)))

(add-to-list 'mc--default-cmds-to-run-once 'mc/remove-current-cursor)

;;;###autoload
(defun mc/remove-duplicated-cursors ()
  "Remove duplicated fake cursors, including ones that overlap the real cursor."
  (interactive)
  (mapc 'mc/remove-fake-cursor
        (loop with seen = (list (point))
              for cursor in (mc/all-fake-cursors)
              for start = (overlay-start cursor)
              append
              (if (loop for pos in seen thereis (= pos start))
                  (list cursor)
                (setq seen (cons start seen))
                nil))))

(add-to-list 'mc--default-cmds-to-run-once 'mc/remove-duplicated-cursors)

;;;###autoload
(defun mc/remove-cursors-at-eol ()
  "Remove cursors at EOL, either fake or real."
  (interactive)
  (loop for cursor in (mc/all-fake-cursors)
        for start = (overlay-start cursor)
        do (if (save-excursion (goto-char start) (eolp))
               (mc/remove-fake-cursor cursor)))
  (if (eolp)
      (ignore-errors
        (mc/remove-current-cursor))))

(add-to-list 'mc--default-cmds-to-run-once 'mc/remove-cursors-at-eol)

(provide 'mc-remove)

;;; mc-remove.el ends here
