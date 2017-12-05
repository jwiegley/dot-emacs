;;; mc-mark-extras.el --- Functions to mark adjacent sexps.

;; Copyright (c) 2017 Akinori MUSHA
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
;; Created: 25 Aug 2017
;; Package-Requires: ((multiple-cursors "1.2.1"))
;; Keywords: editing, cursors

;;; Commentary:
;;
;; This library contains functions to mark sexps in multiple-cursors
;; mode.
;;
;; Suggested key bindings are as follows:
;;
;;   (define-key mc/keymap (kbd "C-. M-C-f") 'mc/mark-next-sexps)
;;   (define-key mc/keymap (kbd "C-. M-C-b") 'mc/mark-previous-sexps)
;;   (define-key mc/keymap (kbd "C-. <") 'mc/mark-all-above)
;;   (define-key mc/keymap (kbd "C-. >") 'mc/mark-all-below)

;;; Code:

(require 'cl)
(require 'multiple-cursors-core)

(defun mc/mark-sexps (num-sexps direction)
  (dotimes (i (if (= num-sexps 0) 1 num-sexps))
    (mc/save-excursion
     (let ((furthest-cursor (cl-ecase direction
                              (forwards  (mc/furthest-cursor-after-point))
                              (backwards (mc/furthest-cursor-before-point)))))
       (when (overlayp furthest-cursor)
         (goto-char (overlay-get furthest-cursor 'point))
         (when (= num-sexps 0)
           (mc/remove-fake-cursor furthest-cursor))))
     (cl-ecase direction
       (forwards (forward-sexp 2) (backward-sexp 1))
       (backwards (backward-sexp 2) (forward-sexp 1)))
     (mc/create-fake-cursor-at-point))))

;;;###autoload
(defun mc/mark-next-sexps (arg)
  "Mark next ARG sexps."
  (interactive "p")
  (mc/mark-sexps arg 'forwards)
  (mc/maybe-multiple-cursors-mode))
(add-to-list 'mc--default-cmds-to-run-once 'mc/mark-next-sexps)

;;;###autoload
(defun mc/mark-previous-sexps (arg)
  "Mark previous ARG sexps."
  (interactive "p")
  (mc/mark-sexps arg 'backwards)
  (mc/maybe-multiple-cursors-mode))

(add-to-list 'mc--default-cmds-to-run-once 'mc/mark-previous-sexps)

;;;###autoload
(defun mc/mark-all-below ()
  "Mark lines below until the cursor hits a line shorter than the current column position."
  (interactive)
  (save-excursion
    (let ((col (current-column)))
      (loop while (and (zerop (forward-line 1))
                       (not (eobp))
                       (= (move-to-column col) col)
                       (not (and (zerop col)
                                 (eolp))))
            do (mc/create-fake-cursor-at-point))
      (mc/maybe-multiple-cursors-mode))))

(add-to-list 'mc--default-cmds-to-run-once 'mc/mark-all-below)

;;;###autoload
(defun mc/mark-all-above ()
  "Mark lines above until the cursor hits a line shorter than the current column position."
  (interactive)
  (save-excursion
    (let ((col (current-column)))
      (loop while (and (zerop (forward-line -1))
                       (not (bobp))
                       (= (move-to-column col) col)
                       (not (and (zerop col)
                                 (eolp))))
            do (mc/create-fake-cursor-at-point))
      (mc/maybe-multiple-cursors-mode))))

(add-to-list 'mc--default-cmds-to-run-once 'mc/mark-all-above)

(provide 'mc-mark-extras)

;;; mc-mark-extras.el ends here
