;;; vertical-consistency.el -- make opposite vertical movement go back its track
;; -----------------------------------------------------------------------------
;;
;; Copyright (C) 2008,2012 David Andersson
;;
;; This file is NOT part of Emacs.
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, 
;; MA 02110-1301, USA.
;;
;;-------------------------------------------------------------------
;;
;; Author: David Andersson <l.david.andersson(at)sverige.nu>
;; Created: 2008-10-17
;; Version: 0.2
;;
;;; Commentary:
;;
;; Scrolling
;; ---------
;; When scrolling X steps in one direction, let scrolling in X steps in
;; the other direction move point back to exactly where it was.
;; As you have notices, the Emacs functions `scroll-up' and `scroll-down'
;; does not do that.
;;
;; Remap your scroll keys to `vert-forward-scroll' and `vert-backward-scroll'.
;;
;; Vertical by line
;; ----------------
;; When moving cursor vertically X lines in one direction, let moving
;; X lines in the other direction move back to exactly where it was.
;;
;; Uh? Isn't this exactly what the Emacs commands `previous-line' and
;; `next-line' do? Yes, it often is. Except when point is in the first
;; or last line of the buffer. When point is somewhere on the first line
;; (and `line-move-visual' is nil) by default C-p will move point to the
;; beginning of the same line, but a subsequent C-n will move point to the
;; second line. Similarly, when point is on the last line (and it is
;; non-empty, i.e. it does not end with a newline) by default C-n will
;; move point to the end of the line, but a subsequent C-p will move
;; point to the second to last line.
;;
;; Remap your up and down arrow keys to `vert-previous-line' and 
;; `vert-next-line'.
;;
;; Usage examples
;; --------------
;; Example init file for Function Key junkies
;;
;;  (require 'vertical-consistency)
;;  (global-set-key [(up)]		'vert-previous-line)
;;  (global-set-key [(down)]		'vert-next-line)
;;  (global-set-key [(prior)]		'vert-backward-scroll)
;;  (global-set-key [(next)]		'vert-forward-scroll)
;;
;; Example init file for Control freaks
;;
;;  (require 'vertical-consistency)
;;  (global-set-key "\C-p"		'vert-previous-line)
;;  (global-set-key "\C-n"		'vert-next-line)
;;  (global-set-key "\M-v"		'vert-backward-scroll)
;;  (global-set-key "\C-v"		'vert-forward-scroll)
;;
;; Example init file for Mouse users
;;
;;  (require 'vertical-consistency)
;;  (global-set-key [mouse-4]		'vert-backward-scroll)
;;  (global-set-key [mouse-5]		'vert-forward-scroll)
;;  (global-set-key [mode-line mouse-4] 'vert-backward-scroll)
;;  (global-set-key [mode-line mouse-5] 'vert-forward-scroll)
;;
;; Compatibility
;; -------------
;; Works with GNU Emacs 22 and 23 and XEmacs 21.
;; Needs package scroll-margs.el if variable vert-scroll-in-place is set.
;;
;; Bugs
;; ----
;; * The scroll functions count text lines, not screen lines. If there
;;   are many very long lines, scrolling may move more than a screenfull
;;   and visual continuity is lost. (It still moves consistently,
;;   so opposite movement returns to the starting point.)
;;
;;-------------------------------------------------------------------
;;
;; History:
;;
;;  0.2 (2012-05-07) David Andersson
;;    Consider line-move-visual, autoload, comments
;;  0.1 (2008-10-17) David Andersson
;;    First extracted from big init file into a package of its own
;;
;;-------------------------------------------------------------------
;;todo: support scroll-other-window ?
;;todo: also set next-screen-context-lines ?
;;todo: customization with defcustom ? (does anyone ever _use_ that "gui"?)
;;todo: change file name to be max 13 chars long ?
;;-------------------------------------------------------------------

;;; Code:

;;-------------------------------------------------------------------
;; Customization variables
;;-------------------------------------------------------------------

(defvar vert-scroll-in-place nil
  "If non-nil: keep cursor position fixed while the text is scrolling.
\(Requires package `scroll-margs' to be loaded.)
If nil: scroll text so that the cursor is at the center of the screen.")

(defvar vert-scroll-amount 0.5
  "The fraction of the window height to scroll. A number between 0.0 and 1.0.
If nil: use `next-screen-context-lines' to compute scroll amount.")

;;-------------------------------------------------------------------
;; Internal variable
;;-------------------------------------------------------------------

(defvar vert--pos-before-scroll nil
  "Internal variable: remember position before scroll that ended at BOF or EOF")
(make-variable-buffer-local 'vert--pos-before-scroll)


;;-------------------------------------------------------------------
;; Helper function
;;-------------------------------------------------------------------

(defun vert-scroll-amount ()
  (if (floatp vert-scroll-amount)
      ;; compute scroll amount as fraction of window size
      (round (* (1- (window-height)) vert-scroll-amount))
    ;; else use same scroll amount as built in scroll-up and scroll-down
    (- (window-height) 1 next-screen-context-lines)))

;;-------------------------------------------------------------------
;; Move by line commands
;;-------------------------------------------------------------------

;;;###autoload
(defun vert-next-line (n)
  "Move vertically N lines down.
Differs from `next-line' in that it movements in opposite directions
are symmetrical at beginning and end of buffer.
\nDon't call this from programs. It catches begin/end-of-buffer errors."
  (interactive "p")
  (if (and (< n 0) ; backward
	   (eobp)
	   (memq last-command '(next-line previous-line))
	   (< temporary-goal-column (current-column)))
      (setq n (1+ n)))
  (if (and (> n 0) ; forward
	   (bobp)
	   (not (eolp))
	   (memq last-command '(next-line previous-line))
	   (> temporary-goal-column (current-column)))
      (setq n (1- n)))
  (condition-case nil
      (next-line n)
    ((beginning-of-buffer end-of-buffer) (ding)))
  (setq this-command 'next-line)) 	; keep goal column

;;;###autoload
(defun vert-previous-line (n)
  "Move vertically N lines up.
Differs from `previous-line' in that it movements in opposite directions
are symmetrical at beginning and end of buffer.
\nDon't call this from programs. It catches begin/end-of-buffer errors."
  (interactive "p")
  (vert-next-line (- n)))

;;--------------------------------------------------------------------
;; Scroll commands
;;--------------------------------------------------------------------

;;;###autoload
(defun vert-backward-scroll (n)
  "Move vertical half a screen upward.
\nDon't call this from programs. It catches begin/end-of-buffer errors."
  (interactive "p")
  (vert-forward-scroll (- n)))

;;;###autoload
(defun vert-forward-scroll (n)
  "Move vertical half a screen downward.
\nDon't call this from programs. It catches begin/end-of-buffer errors."
  (interactive "p")
  (if (and (boundp 'scroll-in-place) scroll-in-place)
      ;; If scroll-in-place is loaded, use it (nothing else would work)
      (if (< n 0) (scroll-down) (scroll-up))
    ;; else
    (if (not (eq last-command 'next-line)) (setq vert--pos-before-scroll nil))
    (if (not (or (bobp) (eobp))) (setq vert--pos-before-scroll (point)))
    (cond ((and vert--pos-before-scroll (eq last-command 'next-line)
		(eq n 1) (bobp))
	   (goto-char vert--pos-before-scroll))
	  ((and vert--pos-before-scroll (eq last-command 'next-line)
		(eq n -1) (eobp))
	   (goto-char vert--pos-before-scroll))
	  ((let ((goal-line (if (and vert-scroll-in-place
				    (fboundp 'scroll-margs-curr-line))
			       (scroll-margs-curr-line)
			     ;; else
			     (/ (- (window-height) 2) 2))))
	    (condition-case nil
		(let ((line-move-visual nil))
		  (next-line (* n (vert-scroll-amount))))
	      ((beginning-of-buffer end-of-buffer) (ding)))
	    (if (and goal-line (not (eobp)))
		(recenter goal-line)))))
    (setq this-command 'next-line)))	; keep goal column

(provide 'vertical-consistency)

;;; vertical-consistency.el ends here
