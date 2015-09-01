;;; unify-buffer.el --- Concatenate multiple buffers
;; $Id: unify-buffer.el,v 1.6 2008/12/02 09:17:35 rubikitch Exp $

;; Copyright (C) 2008  rubikitch

;; Author: rubikitch <rubikitch@ruby-lang.org>
;; Keywords: convenience
;; URL: http://www.emacswiki.org/cgi-bin/wiki/download/unify-buffer.el

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; Concatenate multiple buffers into one buffer.
;; It is useful to view multiple buffers simultaneously.

;;; Commands:
;;
;; Below are complete command list:
;;
;;  `unify-buffers'
;;    Concatenate multiple buffers into one big buffer. Then display it.
;;  `unify-file-buffers'
;;    Concatenate multiple file buffers into one big buffer. Then display it.
;;  `unify-buffer-goto'
;;    Go to the original buffer.
;;  `unify-buffers-mode'
;;    Unify buffers minor mode.
;;
;;; Customizable Options:
;;
;; Below are customizable option list:
;;

;; This package provides two commands:
;;  `unify-buffers': unifies buffers
;;  `unify-file-buffers': unifies buffers with file-name
         
;;; Bug Report:
;;
;; If you have problem, send a bug report via M-x unify-buffers-send-bug-report.
;; The step is:
;;  0) Setup mail in Emacs, the easiest way is:
;;       (setq user-mail-address "your@mail.address")
;;       (setq user-full-name "Your Full Name")
;;       (setq smtpmail-smtp-server "your.smtp.server.jp")
;;       (setq mail-user-agent 'message-user-agent)
;;       (setq message-send-mail-function 'message-smtpmail-send-it)
;;  1) Be sure to use the LATEST version of unify-buffers.el.
;;  2) Enable debugger. M-x toggle-debug-on-error or (setq debug-on-error t)
;;  3) Use Lisp version instead of compiled one: (load "unify-buffers.el")
;;  4) Do it!
;;  5) If you got an error, please do not close *Backtrace* buffer.
;;  6) M-x unify-buffers-send-bug-report and M-x insert-buffer *Backtrace*
;;  7) Describe the bug using a precise recipe.
;;  8) Type C-c C-c to send.
;;  # If you are a Japanese, please write in Japanese:-)

;;; History:

;; $Log: unify-buffer.el,v $
;; Revision 1.6  2008/12/02 09:17:35  rubikitch
;; `unify-buffer-next-header', `unify-buffer-previous-header': Display at the top of the window.
;;
;; Revision 1.5  2008/11/27 19:33:23  rubikitch
;; Implemented `unify-buffer-goto'
;;
;; Revision 1.4  2008/11/27 19:12:16  rubikitch
;; New command: `unify-buffer-next-header', `unify-buffer-previous-header'
;; Renamed command: `unify-buffers-goto' -> `unify-buffer-goto'
;;
;; Revision 1.3  2008/11/27 13:06:44  rubikitch
;; added commentary
;;
;; Revision 1.2  2008/11/27 10:16:14  rubikitch
;; New command `unify-file-buffers'
;;
;; Revision 1.1  2008/11/27 10:10:12  rubikitch
;; Initial revision
;;

;;; Code:

(defvar unify-buffer-version "$Id: unify-buffer.el,v 1.6 2008/12/02 09:17:35 rubikitch Exp $")
(eval-when-compile (require 'cl))

(defface unify-buffer-header-face
  '((t (:background "white" :foreground "black" :weight bold)))
  "Face for the header."
  )

(defmacro ub-aif (test-form then-form &rest else-forms)
  "Anaphoric if. Temporary variable `it' is the result of test-form."
  `(let ((it ,test-form))
     (if it ,then-form ,@else-forms)))  
(put 'ub-aif 'lisp-indent-function 2)

;; (unify-buffers "test" "*scratch*" "unify-buffer.el")
;; (kill-buffer "test")
(defun unify-buffers (&optional unify-buffer-name &rest buffers)
  "Concatenate multiple buffers into one big buffer. Then display it."
  (interactive)
  (unless buffers
    (setq buffers
          (loop for b = (read-buffer "Unify Buffer: " "")
                until (string= b "")
                collect b)))
  (unless unify-buffer-name
    (setq unify-buffer-name
          (read-string "Unify Buffer name: " nil nil "*Unify Buffer*")))
  (pop-to-buffer (apply 'unify-buffers-noselect unify-buffer-name buffers)))

(defun unify-buffers-noselect (unify-buffer-name &rest buffers)
  (with-current-buffer (generate-new-buffer unify-buffer-name)
    (dolist (b buffers)
      (setq b (if (stringp b) (get-buffer b) b))
      (insert (propertize (concat (or (buffer-file-name b)
                                      (buffer-name b))
                                  "\n")
                          'face 'unify-buffer-header-face
                          'unify-buffer-header t
                          'unify-buffer-origbuf b
                          'unify-buffer-origfile (buffer-file-name b)))
      (save-excursion (insert-buffer-substring b))
      (put-text-property (point) (point-max) 'unify-buffer-origbuf b)
      (put-text-property (point) (point-max) 'unify-buffer-origfile
                         (buffer-file-name b))
      (goto-char (point-max))
      (unless (bolp)
        (newline)))
    (goto-char (point-min))
    (unify-buffers-mode t)
    (current-buffer)))

;; (unify-file-buffers "unify-files" "~/.emacs" "~/.zshrc" "~/.screenrc")
;; (kill-buffer "unify-files")
(defun unify-file-buffers (&optional unify-buffer-name &rest files)
  "Concatenate multiple file buffers into one big buffer. Then display it."
  (interactive)
  (unless files
    (setq files
          (loop for f = (read-file-name "Unify File Buffer: " nil "")
                until (string= f "")
                collect f)))
  (unless unify-buffer-name
    (setq unify-buffer-name
          (read-string "Unify File Buffer name: " nil nil "*Unify Buffer*")))
  (pop-to-buffer (apply 'unify-file-buffers-noselect unify-buffer-name files)))

(defun unify-file-buffers-noselect (unify-buffer-name &rest files)
  (apply 'unify-buffers-noselect unify-buffer-name
         (mapcar 'find-file-noselect files)))

(defun unify-buffer-header-p (position)
  (get-text-property position 'unify-buffer-header))

(defun unify-buffer-next-header ()
  (interactive)
  (when (unify-buffer-header-p (point))
    (forward-line 1))
  (ub-aif (next-single-property-change (point) 'unify-buffer-header)
      (goto-char it)
    (forward-line -1))
  (recenter 0))

(defun unify-buffer-previous-header ()
  (interactive)
  (when (unify-buffer-header-p (point))
    (forward-line -1))
  (ub-aif (previous-single-property-change (point) 'unify-buffer-header)
      (goto-char it))
  (forward-line -1)
  (recenter 0))

(defun unify-buffer-goto ()
  "Go to the original buffer."
  (interactive)
  (let ((origpt (point))
        (pt (if (unify-buffer-header-p (point))
                1
              (- (point) (previous-single-property-change (point) 'unify-buffer-header) -1)))
        (wstart (window-start))
        (origbuf (get-text-property (point) 'unify-buffer-origbuf))
        (origfile (get-text-property (point) 'unify-buffer-origfile)))
    (if origfile
        (find-file origfile)
      (switch-to-buffer origbuf))
    (goto-char pt)
    (set-window-start (selected-window) (- pt (- origpt wstart)))))

(defvar unify-buffers-mode-map (make-sparse-keymap))
(define-key unify-buffers-mode-map "\C-m" 'unify-buffer-goto)
(define-key unify-buffers-mode-map "}" 'unify-buffer-next-header)
(define-key unify-buffers-mode-map "{" 'unify-buffer-previous-header)


;; unify-buffers-mode is a minor-mode because future version will
;; inherit original major modes.
(define-minor-mode unify-buffers-mode
  "Unify buffers minor mode."
  nil nil unify-buffers-mode-map
  (cond (unify-buffers-mode
         (view-mode 1))
        (t
         (view-mode 0))))

;;;; Bug report
(defvar unify-buffers-maintainer-mail-address
  (concat "rubiki" "tch@ru" "by-lang.org"))
(defvar unify-buffers-bug-report-salutation
  "Describe bug below, using a precise recipe.

When I executed M-x ...

How to send a bug report:
  1) Be sure to use the LATEST version of unify-buffers.el.
  2) Enable debugger. M-x toggle-debug-on-error or (setq debug-on-error t)
  3) Use Lisp version instead of compiled one: (load \"unify-buffers.el\")
  4) If you got an error, please paste *Backtrace* buffer.
  5) Type C-c C-c to send.
# If you are a Japanese, please write in Japanese:-)")
(defun unify-buffers-send-bug-report ()
  (interactive)
  (reporter-submit-bug-report
   unify-buffers-maintainer-mail-address
   "unify-buffers.el"
   (apropos-internal "^unify-buffers-" 'boundp)
   nil nil
   unify-buffers-bug-report-salutation))

(provide 'unify-buffer)

;; How to save (DO NOT REMOVE!!)
;; (emacswiki-post "unify-buffer.el")
;;; unify-buffer.el ends here
