;;; mc-cua.el --- Make multiple-cursors interact with CUA mode.

;; Copyright (c) 2013 Akinori MUSHA
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
;; Created: 16 Jul 2013
;; Package-Requires: ((multiple-cursors "1.2.1"))
;; Keywords: editing, cursors

;;; Commentary:
;;
;; This library contains functions to make multiple-cursors interact
;; with CUA mode.
;;
;; Suggested key bindings are as follows:
;;
;;   (define-key cua--rectangle-keymap (kbd "C-. C-,") 'mc/cua-rectangle-to-multiple-cursors)
;;
;; To enable interaction between multiple cursors and CUA rectangle
;; copy & paste:
;;
;;   (mc/cua-rectangle-setup)


;;; Code:

(require 'cl)
(require 'multiple-cursors-core)
(require 'cua-rect)

;;;###autoload
(defun mc/cua-rectangle-to-multiple-cursors ()
  "Turn CUA rectangle mode into multiple-cursors mode, keeping insert positions and selections."
  (interactive)
  (let ((right (cua--rectangle-right-side))
        rows)
    (cua--rectangle-operation
        'clear nil t nil nil
        (lambda (s e _l _r)
          (setq rows
                (append rows
                        (list (cons (+ 0 s) (+ 0 e)))))))
    (cua--cancel-rectangle)
    (if rows
        (let ((mark-row `(lambda (row)
                           ,@(if right
                                 '((push-mark (car row))
                                   (goto-char (cdr row)))
                               '((push-mark (cdr row))
                                 (goto-char (car row))))
                           (setq transient-mark-mode (cons 'only transient-mark-mode))
                           (activate-mark)
                           (setq deactivate-mark nil)))
              (top (car rows))
              (rest (cdr rows)))
          (loop for row in rest do
                (mc/save-excursion
                 (funcall mark-row row)
                 (mc/create-fake-cursor-at-point)))
          (funcall mark-row top)
          (mc/maybe-multiple-cursors-mode)))))

(add-to-list 'mc--default-cmds-to-run-once 'mc/cua-rectangle-to-multiple-cursors)

;;
;; Build a CUA rectangle from entries copied with multiple cursors.
;;

(defadvice mc--maybe-set-killed-rectangle
  (around mc/cua-set-last-killed-rectangle)
  "Set `cua--last-killed-rectangle' as well as `killed-rectangle'."
  (if (boundp 'cua--last-killed-rectangle)
      (let ((orig-entries killed-rectangle))
        ad-do-it
        (when (not (eq orig-entries killed-rectangle))
          (setq cua--last-killed-rectangle
                (cons (car kill-ring) killed-rectangle))))
    ad-do-it))

;;
;; Let each of multiple cursors paste the corresponding line of the
;; last killed rectangle.
;;

(defvar mc/cua-saved-kill-ring nil)

(defadvice current-kill
  (before mc/cua-remember-kill-ring)
  "Remember `kill-ring' before interprogram-paste."
  (setq mc/cua-saved-kill-ring kill-ring))

(defadvice current-kill
  (after mc/cua-clear-last-killed-rectangle-on-interprogram-paste)
  "Clear `cua--last-killed-rectangle' on interprogram paste."
  (and (= n 0)
       interprogram-paste-function
       (boundp 'cua--last-killed-rectangle)
       cua--last-killed-rectangle
       (not (eq mc/cua-saved-kill-ring kill-ring))
       (setq cua--last-killed-rectangle nil))
  (setq mc/cua-saved-kill-ring nil))

(defadvice cua-paste
  (before mc/cua-divide-rectangle-into-lines)
  "Let each of multiple cursors paste the corresponding line of the last killed rectangle."
  (and (null arg)       ;; Currently no support for register 0-9.
       (or (null kill-ring)
           (current-kill 0)) ;; Take interprogram paste into account.
       cua--last-killed-rectangle
       multiple-cursors-mode
       (let ((rect (cdr cua--last-killed-rectangle)))
         (mc/for-each-cursor-ordered
          (let ((kill-ring (overlay-get cursor 'kill-ring))
                (kill-ring-yank-pointer (overlay-get cursor 'kill-ring-yank-pointer)))
            (kill-new (or (pop rect) ""))
            (overlay-put cursor 'kill-ring kill-ring)
            (overlay-put cursor 'kill-ring-yank-pointer kill-ring-yank-pointer)))
         (setq cua--last-killed-rectangle nil))))

;;;###autoload
(defun mc/cua-rectangle-setup ()
  "Enable interaction between multiple cursors and CUA rectangle copy & paste."
  (ad-activate 'mc--maybe-set-killed-rectangle)
  (ad-activate 'current-kill)
  (ad-activate 'cua-paste))

(provide 'mc-cua)

;;; mc-cua.el ends here
