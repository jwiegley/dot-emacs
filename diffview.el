;;; diffview.el --- View diffs in side-by-side format

;; Copyright (C) 2013-2015, Mitchel Humpherys

;; Author: Mitchel Humpherys <mitch.special@gmail.com>
;; Maintainer: Mitchel Humpherys <mitch.special@gmail.com>
;; Keywords: convenience, diff
;; Version: 1.0
;; URL: https://github.com/mgalgs/diffview-mode

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
;;
;; Render a unified diff (top/bottom) in an easy-to-comprehend side-by-side
;; format.  This comes in handy for reading patches from mailing lists (or
;; from whencever you might acquire them).
;;
;;; Installation:
;;
;;     M-x package-install diffview
;;
;;; Usage:
;;
;; The following functions are provided for launching a side-by-side diff:
;;
;; o `diffview-current' : View the current diff buffer side-by-side
;; o `diffview-region' : View the current diff region side-by-side
;; o `diffview-message' : View the current email message (which presumably
;;    contains a patch) side-by-side
;;
;;
;;; Screenshots:
;;
;; Before:
;; https://raw.github.com/mgalgs/diffview-mode/master/screenshots/diffview-before.png
;;
;; After:
;; https://raw.github.com/mgalgs/diffview-mode/master/screenshots/diffview-after.png
;;
;;; Code:

(require 'message)

(defun diffview--print-all-lines-to-buffer (lines buffer-name)
  "Prints each line in `LINES' to a buffer named `BUFFER-NAME'."
  (let ((old-temp-buffer (get-buffer buffer-name)))
    ;; (with-output-to-temp-buffer buffer-name
    (when old-temp-buffer
      (kill-buffer old-temp-buffer))
    (with-current-buffer (get-buffer-create buffer-name)
      (erase-buffer)
      (dolist (line lines)
	(insert line "\n")))))

(defvar diffview--minus-bufname "*side-by-side-1*")
(defvar diffview--plus-bufname "*side-by-side-2*")
(defvar diffview--saved-wincfg nil)
(defvar diffview--regexp-is-plus-line "^\\+\\([^+]\\{1\\}\\|$\\)"
  "A + followed by one non + or the end of the line.")
(defvar diffview--regexp-is-minus-line "^-\\([^-]\\{1\\}\\|$\\)"
  "A - followed by one non - or the end of the line.")

(defun diffview--view-string (input-string)
  "Displays `INPUT-STRING' (a diff) in a side-by-side view."
  (setq diffview--saved-wincfg (current-window-configuration))
  (delete-other-windows)
  (let (plus-lines
	minus-lines
	tmp-line
	(current-state 'in-common)
	(last-state 'in-common)
	(current-lines-in-plus 0)
	(current-lines-in-minus 0)
	(total-lines 0)
	(all-lines (split-string input-string "\n")))
    (dolist (line all-lines)
      (cond
       ((string-match diffview--regexp-is-plus-line line)
	(push line plus-lines)
	(setq current-state 'in-plus)
	(setq current-lines-in-plus (1+ current-lines-in-plus)))
       ((string-match diffview--regexp-is-minus-line line)
	(push line minus-lines)
	(setq current-state 'in-minus)
	(setq current-lines-in-minus (1+ current-lines-in-minus)))
       ;; everything else must be common
       (t
	(push line plus-lines)
	(push line minus-lines)
	(setq current-state 'in-common)))

      (setq total-lines (1+ total-lines))

      ;; Process hunk state transitions
      (when (not (equal current-state last-state))
	;; there's been a state change
	(when (equal current-state 'in-common)
	  ;; we're transitioning out the +/- part of a hunk. We would
	  ;; like both sides to have the same number lines for this
	  ;; hunk, so we might need to fill one side or the other with
	  ;; empty lines.
	  (cond
	   ((> current-lines-in-plus current-lines-in-minus)
	    ;; need to fill minus
	    (setq tmp-line (pop minus-lines))
	    (dotimes (i (- current-lines-in-plus current-lines-in-minus))
	      (push "" minus-lines))
	    (push tmp-line minus-lines))
	   ((< current-lines-in-plus current-lines-in-minus)
	    ;; need to fill plus
	    (setq tmp-line (pop plus-lines))
	    (dotimes (i (- current-lines-in-minus current-lines-in-plus))
	      (push "" plus-lines))
	    (push tmp-line plus-lines)))

	  (setq current-lines-in-plus  0
		current-lines-in-minus 0)))

      (setq last-state current-state))

    (diffview--print-all-lines-to-buffer (reverse minus-lines) diffview--minus-bufname)
    (diffview--print-all-lines-to-buffer (reverse plus-lines) diffview--plus-bufname)

    (switch-to-buffer diffview--minus-bufname nil t)
    (goto-char (point-min))
    (diffview-mode)

    (split-window-right)
    (other-window 1)

    (switch-to-buffer diffview--plus-bufname nil t)
    (goto-char (point-min))
    (diffview-mode)

    (scroll-all-mode)))

;;;###autoload
(defun diffview-current ()
  "Show current diff buffer in a side-by-side view."
  (interactive)
  (diffview--view-string (buffer-string)))

;;;###autoload
(defun diffview-region ()
  "Show current diff region in a side-by-side view."
  (interactive)
  (diffview--view-string (buffer-substring (point) (mark))))

;;;###autoload
(defun diffview-message ()
  "Show `message-mode' buffer in a side-by-side view.

This is useful for reading patches from mailing lists."
  (interactive)
  (let (beg end)
    (save-excursion
      (message-goto-body)
      (search-forward-regexp "^---$")
      (setq beg (1+ (point)))
      (search-forward-regexp "^-- $")
      (setq end (1+ (point)))
      (diffview--view-string (buffer-substring beg end)))))



;;; You probably don't want to invoke `diffview-mode' directly.  Just use
;;; one of the autoload functions above.

(define-derived-mode diffview-mode special-mode "Diffview"
  "Mode for viewing diffs side-by-side"
  (setq font-lock-defaults '(diff-font-lock-keywords t nil nil nil (font-lock-multiline . nil))))

(defun diffview--quit ()
  "Quit diffview and clean up diffview buffers."
  (interactive)
  (delete-other-windows)
  (scroll-all-mode 0)
  (let ((plusbuf (get-buffer diffview--plus-bufname))
	(minusbuf (get-buffer diffview--minus-bufname)))
    (if plusbuf (kill-buffer plusbuf))
    (if minusbuf (kill-buffer minusbuf)))
  (set-window-configuration diffview--saved-wincfg))

(define-key diffview-mode-map (kbd "q") 'diffview--quit)

(provide 'diffview)
;;; diffview.el ends here
;;
