;;; wcount.el --- keep a running count of words in a buffer

;; Copyright 1997 Bob Glickstein.      <http://www.zanshin.com/~bobg/>

;; Author: Bob Glickstein <bobg@zanshin.com>
;; Maintainer: Bob Glickstein <bobg@zanshin.com>
;; Version: 1.0

;; This file is not part of GNU Emacs.

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 2, or (at your
;; option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, send e-mail to
;; this program's maintainer or write to the Free Software Foundation,
;; Inc., 59 Temple Place, Suite 330; Boston, MA 02111-1307, USA.

;;; Plug:

;; Check out my book, "Writing GNU Emacs Extensions," from O'Reilly
;; and Associates.  <http://www.ora.com/catalog/gnuext/>

;;; Commentary:

;; `wcount-mode' is a minor mode that puts into the modeline a running
;; count of the words in the buffer.  Because computing the number of
;; words can be computationally expensive for large buffers, the count
;; is only updated when Emacs has been idle for `wcount-idleness'
;; seconds, or when the user presses C-c w (`wcount-count').

;;; To do:

;; Allow a word syntax different from the one implied by
;; `forward-word'.

;;; Code:

(require 'timer)
(require 'assoc)

(defvar wcount-mode nil)
(make-variable-buffer-local 'wcount-mode)

(defvar wcount-idleness 180
  "*Seconds of idle time before re-counting words in the buffer.")

(defvar wcount-timer nil)
(make-variable-buffer-local 'wcount-timer)

(defvar wcount-mode-line-data nil)
(make-variable-buffer-local 'wcount-mode-line-data)

(aput 'minor-mode-alist 'wcount-mode '(wcount-mode-line-data))

(defvar wcount-mode-map nil)

(if (null wcount-mode-map)
    (progn
      (setq wcount-mode-map (make-sparse-keymap))
      (define-key wcount-mode-map "\C-cw" 'wcount-count)))

(aput 'minor-mode-map-alist 'wcount-mode wcount-mode-map)

(defun wcount-mode (&optional arg)
  "Keep a running count of this buffer's words in the mode line."
  (interactive "P")
  (setq wcount-mode
	(if (null arg)
	    (not wcount-mode)
	  (> (prefix-numeric-value arg) 0)))
  (if (timerp wcount-timer)
      (cancel-timer wcount-timer))
  (if wcount-mode
      (setq wcount-timer (run-with-idle-timer wcount-idleness t 'wcount-count
					      (current-buffer))
	    wcount-mode-line-data " wc[?]")))

(defun wcount-count (&optional buffer)
  (interactive)
  (save-excursion
    (set-buffer (or buffer (current-buffer)))
    (save-restriction
      (widen)
      (goto-char (point-min))
      (let ((result 0))
	(message "Counting words...")
	(while (not (eobp))
	  (forward-word 1)
	  (setq result (1+ result)))
	(message "Counting words... done")
	(setq wcount-mode-line-data
	      (concat " wc[" (int-to-string result) "]"))
	result))))

(provide 'wcount)

;;; wcount.el ends here
