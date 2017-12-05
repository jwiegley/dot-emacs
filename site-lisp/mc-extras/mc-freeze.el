;;; mc-freeze.el --- Freeze and unfreeze fake cursors in multiple-cursors mode.

;; Copyright (c) 2015 Akinori MUSHA
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
;; Created: 18 Feb 2015
;; Package-Requires: ((multiple-cursors "1.2.1"))
;; Keywords: editing, cursors

;;; Commentary:
;;
;; This library contains functions to temporarily freeze fake cursors
;; for later reactivation so you can move the real cursor alone in
;; `multiple-cursors-mode'.
;;
;; Suggested key binding is as follows:
;;
;;   (global-set-key (kbd "C-. C-.") 'mc/freeze-fake-cursors-dwim)

;;; Code:

(eval-when-compile
  (require 'cl))
(require 'multiple-cursors-core)

(defvar mc-freeze--frozen-cursors nil
  "Keeps a list of frozen fake cursors to be reactivated later.")
(make-variable-buffer-local 'mc-freeze--frozen-cursors)

(defun mc-freeze--frozen-cursor-p (ov)
  (eq (overlay-get ov 'type) 'mc-freeze--frozen-cursor))

(defun mc-freeze--frozen-cursor-at-pos-p (pos)
  (loop for ov in (overlays-at pos)
        thereis (mc-freeze--frozen-cursor-p ov)))

(defun mc-freeze--add-frozen-cursor (pos)
  (or
   (mc-freeze--frozen-cursor-at-pos-p pos)
   (let ((ov (make-overlay pos (1+ pos) nil nil nil)))
     (overlay-put ov 'type 'mc-freeze--frozen-cursor)
     (overlay-put ov 'face 'mc/cursor-face)
     (add-to-list 'mc-freeze--frozen-cursors ov))))

;;;###autoload
(defun mc/freeze-fake-cursors (&optional arg)
  "Freeze fake cursors for later reactivation.

With ARG or when there is no fake cursor, create a fake cursor at
point before freezing fake cursors."
  (interactive "P")
  (when (or arg
            (and
             (null mc-freeze--frozen-cursors)
             (= (mc/num-cursors) 1)))
    (mc/create-fake-cursor-at-point))
  (when (> (mc/num-cursors) 1)
    (mc/for-each-fake-cursor
     (mc-freeze--add-frozen-cursor (overlay-start cursor)))
    (mc/remove-fake-cursors)
    (message "Time stop!")))

(add-to-list 'mc--default-cmds-to-run-once 'mc/freeze-fake-cursors)

;;;###autoload
(defun mc/unfreeze-fake-cursors ()
  "Unfreeze frozen fake cursors."
  (interactive)
  (loop for ov in mc-freeze--frozen-cursors do
        (let ((pos (overlay-start ov)))
          (delete-overlay ov)
          (and (/= pos (point))
               (loop for o in (overlays-at pos)
                     never (mc/fake-cursor-p o))
               (mc/save-excursion
                (goto-char pos)
                (mc/create-fake-cursor-at-point)))))
  (setq mc-freeze--frozen-cursors nil)
  (mc/maybe-multiple-cursors-mode)
  ;; Prevent the fake cursors from moving via mc's post-command-hook
  (setq this-original-command nil)
  (message "And time resumes."))

(add-to-list 'mc--default-cmds-to-run-once 'mc/unfreeze-fake-cursors)

;;;###autoload
(defun mc/freeze-fake-cursors-dwim (&optional arg)
  "Freeze or unfreeze fake cursors depending on the current state.

With ARG, always create a fake cursor at point then freeze fake
cursors."
  (interactive "P")
  (cond ((> (mc/num-cursors) 1)
         (mc/freeze-fake-cursors arg))
        ((or arg
             (null mc-freeze--frozen-cursors))
         (mc/freeze-fake-cursors t))
        (t
         (mc/unfreeze-fake-cursors))))

(add-to-list 'mc--default-cmds-to-run-once 'mc/freeze-fake-cursors-dwim)

(provide 'mc-freeze)

;;; mc-freeze.el ends here
