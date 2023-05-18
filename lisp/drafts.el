;;; drafts.el --- Write text first, act on it after

;; Copyright (C) 2023 John Wiegley <johnw@gnu.org>

;; Emacs Lisp Archive Entry
;; Filename: drafts.el
;; Version: 1.0
;; Keywords: text draft productivity
;; Author: John Wiegley <johnw@gnu.org>
;; Maintainer: John Wiegley <johnw@gnu.org>
;; Description: Write text first, act on it after
;; URL: https://github.com/jwiegley/drafts
;; Compatibility: Emacs28

;; This file is not part of GNU Emacs.

;; This is free software; you can redistribute it and/or modify it under
;; the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2, or (at your option) any later
;; version.
;;
;; This is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
;; for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
;; MA 02111-1307, USA.

;;; Commentary:

;; Use case:
;;
;; User types `M-x drafts', one of the two things happen:
;;
;; 1. If it has been more than `drafts-reset-delay-seconds' since the last
;;    time the latest drafts buffer was visited, a new, empty buffer is
;;    created with major-mode set to `drafts-default-major-mode'.
;;
;; 2. If it has been less than that amount of time, revisit the latest drafts
;;    buffer.
;;
;; Old, empty drafts buffer are garbage collected.
;;
;; Each drafts buffer is associated with a file in the `drafts-directory',
;; whose name is formed from the timestamp when the draft was created.
;; Auto-saving is aggresively enabled in these buffers so that they are saved
;; very often, and also whenever focus moves away from the buffer.
;;
;; In the drafts buffer, the following key bindings are available through the
;; `drafts-mode-map':
;;
;; `C-c C-k' :: Kill the current drafts buffer and delete its associated file.
;;              Prompts if `drafts-prompt-before-delete' is non-nil.
;;
;; `C-c C-c' :: "Act" on the content of the current drafts buffer. See below.
;;
;; When a draft is killed or acted on, the original file containing the draft
;; is archived to `drafts-archive-directory'. To avoid archiving killed
;; drafts, set `drafts-archive-when-killed' to `nil'.
;;
;; The command `M-x drafts-browse' will open the `drafts-directory' in dired,
;; so that you can manage or revisit those files directly. Each file bears the
;; extension ".draft" in order to know that the default major-mode and drafts
;; minor-mode should be active.

(eval-when-compile
  (require 'cl))

(defgroup drafts nil
  "Edit and act on textual drafts"
  :group 'text)

(defsubst drafts--filter (f args)
  (let (result)
    (dolist (arg args)
      (when (funcall f arg)
        (setq result (cons arg result))))
    (nreverse result)))

(defvar drafts-last-visited-time nil)
(make-variable-buffer-local 'drafts-last-visited-time)

(defun drafts-last-visited-time ()
  (sort
   (mapcar
    #'(lambda (buf)
        (cons buf
              (with-current-buffer buf
                drafts-last-visited-time)))
    (drafts--filter
     #'(lambda (buf)
         (string-match "\\*drafts\\*" (buffer-name buf)))
     (buffer-list)))
   #'(lambda (x y)
       (> (cdr x) (cdr y)))))

(define-minor-mode drafts-mode
  "Minor mode active in drafts buffers."
  :lighter " drafts"
  :global t
  :group 'drafts
  (add-hook 'post-command-hook
            #'(lambda (&rest _ignore)
                (setq drafts-last-visited-time (current-time)))
            nil t))

(defun drafts (&optional arg)
  (interactive "p")
  (if (or (not drafts-last-visited-time)
          (> (float-time
              (time-subtract (current-time)
                             drafts-last-visited-time))
             30.0))
      t
    t))

(provide 'drafts)
