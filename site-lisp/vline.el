;;; vline.el --- show vertical line (column highlighting) mode.

;; Copyright (C) 2002, 2008-2012 by Taiki SUGAWARA <buzz.taiki@gmail.com>

;; Author: Taiki SUGAWARA <buzz.taiki@gmail.com>
;; Maintainer: Taiki SUGAWARA <buzz.taiki@gmail.com>
;; Keywords: faces, editing, emulating
;; Version: 1.11
;; Time-stamp: <2012-01-08 12:40:18 UTC taiki>
;; URL: http://www.emacswiki.org/cgi-bin/wiki/vline.el
;; URL: http://bitbucket.org/buzztaiki/elisp/src/tip/vline.el

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

;; put followings your .emacs
;;   (require 'vline)
;;
;; if you display a vertical line, type M-x vline-mode.  `vline-mode' doesn't
;; effect other buffers, because it is a buffer local minor mode.  if you hide
;; a vertical line, type M-x vline-mode again.
;;
;; if you display a vertical line in all buffers, type M-x vline-global-mode.
;;
;; `vline-style' provides a display style of vertical line.  see
;; `vline-style' docstring.
;;
;; if you don't want to visual line highlighting (ex.  for performance
;; issue), please to set `vline-visual' to nil.
;;
;; if you don't want to use timer (ex.  you want to highlight column
;; during moving cursors), please to set `vline-use-timer' to nil.

;;; Change Log:

;; 2012-01-08 taiki
;; fix for the Lint warnings.

;; 2010-02-02 taiki
;; improve performance.

;; 2009-08-26 taiki
;; support org-mode, outline-mode

;; 2009-08-18 taiki
;; add autoload cookies.

;; 2009-08-18 taiki
;; fix last line highlighting probrem.

;; 2009-08-18 taiki
;; support visual line highlighting.
;; - Added face vline-visual.
;; - Added defcustom vline-visual-face.
;; - Added defcustom vline-visual.
;;
;; 2009-08-17 taiki
;; fix continuas line problem.
;; - Don't display vline when cursor into fringe
;; - Don't expand eol more than window width.
;;
;; 2008-10-22 taiki
;; fix coding-system problem.
;; - Added vline-multiwidth-space-list
;; - Use ucs code-point for japanese fullwidth space.
;;
;; 2008-01-22 taiki
;; applied patch from Lennart Borgman
;; - Added :group 'vline
;; - Added defcustom vline-current-window-only
;; - Added header items to simplify for users

;;; TODO:
;; - track window-scroll-functions, window-size-change-functions.
;; - consider other minor modes (using {after,before}-string overlay).
;; - don't use {post,after}-command-hook for performance??

;;; Code:

(defvar vline-overlay-table-size 200)
(defvar vline-overlay-table (make-vector vline-overlay-table-size nil))
(defvar vline-line-char ?|)
(defvar vline-multiwidth-space-list
  (list
   ?\t
   (decode-char 'ucs #x3000)		; japanese fullwidth space
   ))
(defvar vline-timer nil)

(defcustom vline-style 'face
  "This variable holds vertical line display style.
Available values are followings:
`face'	    : use face.
`compose'   : use composit char.
`mixed'	    : use face and composit char."
  :type '(radio
	  (const face)
	  (const compose)
	  (const mixed))
  :group 'vline)


(defface vline
  '((t (:background "light steel blue")))
  "A default face for vertical line highlighting."
  :group 'vline)

(defface vline-visual
  '((t (:background "gray90")))
  "A default face for vertical line highlighting in visual lines."
  :group 'vline)

(defcustom vline-face 'vline
  "A face for vertical line highlighting."
  :type 'face
  :group 'vline)

(defcustom vline-visual-face 'vline-visual
  "A face for vertical line highlighting in visual lines."
  :type 'face
  :group 'vline)

(defcustom vline-current-window-only nil
  "If non-nil then highlight column in current window only.
If the buffer is shown in several windows then highlight column only
in the currently selected window."
  :type 'boolean
  :group 'vline)

(defcustom vline-visual t
  "If non-nil then highlight column in visual lines.
If you specified `force' then use force visual line highlighting even
if `truncate-lines' is non-nil."
  :type '(radio
	  (const nil)
	  (const t)
	  (const force))
  :group 'vline)

(defcustom vline-use-timer t
  "If non-nil, use idle timer instead of (post|after)-command-hook."
  :type 'boolean
  :group 'vline)

(defcustom vline-idle-time 0.02
  "Idle time for highlighting column."
  :type 'number
  :group 'vline)

;;;###autoload
(define-minor-mode vline-mode
  "Display vertical line mode."
  :global nil
  :lighter " VL"
  :group 'vline
  (if vline-mode
      (progn
	(add-hook 'pre-command-hook 'vline-pre-command-hook nil t)
	(if vline-use-timer
	    (vline-set-timer)
	  (add-hook 'post-command-hook 'vline-post-command-hook nil t)))
    (vline-cancel-timer)
    (vline-clear)
    (remove-hook 'pre-command-hook 'vline-pre-command-hook t)
    (remove-hook 'post-command-hook 'vline-post-command-hook t)))

;;;###autoload
(define-global-minor-mode vline-global-mode
  vline-mode
  (lambda ()
    (unless (minibufferp)
      (vline-mode 1)))
  :group 'vline)

(defun vline-pre-command-hook ()
  (when (and vline-mode (not (minibufferp)))
    (vline-clear)))

(defun vline-post-command-hook ()
  (when (and vline-mode (not (minibufferp)))
    (vline-show)))

(defun vline-set-timer ()
  (setq vline-timer
	(run-with-idle-timer
	 vline-idle-time t 'vline-timer-callback)))

(defun vline-cancel-timer ()
  (when (timerp vline-timer)
    (cancel-timer vline-timer)))

(defun vline-timer-callback ()
  (when (and vline-mode (not (minibufferp)))
    (vline-show)))

(defun vline-clear ()
  (mapcar (lambda (ovr)
	    (and ovr (delete-overlay ovr)))
	  vline-overlay-table))

(defsubst vline-into-fringe-p ()
  (eq (nth 1 (posn-at-point)) 'right-fringe))

(defsubst vline-visual-p ()
  (or (eq vline-visual 'force)
      (and (not truncate-lines)
	   vline-visual)))

(defsubst vline-current-column ()
  (if (or (not (vline-visual-p))
	  ;; margin for full-width char
	  (< (1+ (current-column)) (window-width)))
      (current-column)
    ;; hmm.. posn-at-point is not consider tab width.
    (- (current-column)
       (save-excursion
	 (vertical-motion 0)
	 (current-column)))))

(defsubst vline-move-to-column (col &optional bol-p)
  (if (or (not (vline-visual-p))
	  ;; margin for full-width char
	  (< (1+ (current-column)) (window-width)))
      (move-to-column col)
    (unless bol-p
      (vertical-motion 0))
    (let ((bol-col (current-column)))
      (- (move-to-column (+ bol-col col))
	 bol-col))))

(defsubst vline-invisible-p (pos)
  (let ((inv (get-char-property pos 'invisible)))
    (and inv
	 (or (eq buffer-invisibility-spec t)
	     (memq inv buffer-invisibility-spec)
	     (assq inv buffer-invisibility-spec)))))

(defsubst vline-forward (n)
  (unless (memq n '(-1 0 1))
    (error "n(%s) must be 0 or 1" n))
  (if (not (vline-visual-p))
      (progn
	(forward-line n)
	;; take care of org-mode, outline-mode
	(when (and (not (bobp))
		   (vline-invisible-p (1- (point))))
	  (goto-char (1- (point))))
	(when (vline-invisible-p (point))
	  (if (< n 0)
	      (while (and (not (bobp)) (vline-invisible-p (point)))
		(goto-char (previous-char-property-change (point))))
	    (while (and (not (bobp)) (vline-invisible-p (point)))
	      (goto-char (next-char-property-change (point))))
	    (forward-line 1))))
    (vertical-motion n)))

(defun vline-face (visual-p)
  (if visual-p
      vline-visual-face
    vline-face))

(defun vline-show (&optional point)
  (vline-clear)
  (save-window-excursion
    (save-excursion
      (if point
	  (goto-char point)
	(setq point (point)))
      (let* ((column (vline-current-column))
	     (lcolumn (current-column))
	     (i 0)
	     (compose-p (memq vline-style '(compose mixed)))
	     (face-p (memq vline-style '(face mixed)))
	     (line-char (if compose-p vline-line-char ? ))
	     (line-str (make-string 1 line-char))
	     (visual-line-str line-str)
	     (in-fringe-p (vline-into-fringe-p)))
	(when face-p
	  (setq line-str (propertize line-str 'face (vline-face nil)))
	  (setq visual-line-str (propertize visual-line-str 'face (vline-face t))))
	(goto-char (window-end nil t))
	(vline-forward 0)
	(while (and (not in-fringe-p)
		    (< i (window-height))
		    (< i (length vline-overlay-table))
		    (not (bobp)))
	  (let ((cur-column (vline-move-to-column column t))
		(cur-lcolumn (current-column)))
	    ;; non-cursor line only (workaround of eol probrem.
	    (unless (= (point) point)
	      ;; if column over the cursor's column (when tab or wide char is appered.
	      (when (> cur-column column)
		(let ((lcol (current-column)))
		  (backward-char)
		  (setq cur-column (- cur-column (- lcol (current-column))))))
	      (let* ((ovr (aref vline-overlay-table i))
		     (visual-p (or (< lcolumn (current-column))
				   (> lcolumn (+ (current-column)
						 (- column cur-column)))))
		     ;; consider a newline, tab and wide char.
		     (str (concat (make-string (- column cur-column) ? )
				  (if visual-p visual-line-str line-str)))
		     (char (char-after)))
		;; create overlay if not found.
		(unless ovr
		  (setq ovr (make-overlay 0 0))
		  (overlay-put ovr 'rear-nonsticky t)
		  (aset vline-overlay-table i ovr))

		;; initialize overlay.
		(overlay-put ovr 'face nil)
		(overlay-put ovr 'before-string nil)
		(overlay-put ovr 'after-string nil)
		(overlay-put ovr 'invisible nil)
		(overlay-put ovr 'window
			     (if vline-current-window-only
				 (selected-window)
			       nil))

		(cond
		 ;; multiwidth space
		 ((memq char vline-multiwidth-space-list)
		  (setq str
			(concat str
				(make-string (- (save-excursion (forward-char)
								(current-column))
						(current-column)
						(string-width str))
					     ? )))
		  (move-overlay ovr (point) (1+ (point)))
		  (overlay-put ovr 'invisible t)
		  (overlay-put ovr 'after-string str))
		 ;; eol
		 ((eolp)
		  (move-overlay ovr (point) (point))
		  (overlay-put ovr 'after-string str)
		  ;; don't expand eol more than window width
		  (when (and (not truncate-lines)
			     (>= (1+ column) (window-width))
			     (>= column (vline-current-column))
			     (not (vline-into-fringe-p)))
		    (delete-overlay ovr)))
		 (t
		  (cond
		   (compose-p
		    (let (str)
		      (when char
			(setq str (compose-chars
				   char
				   (cond ((= (char-width char) 1)
					  '(tc . tc))
					 ((= cur-column column)
					  '(tc . tr))
					 (t
					  '(tc . tl)))
				   line-char))
			(when face-p
			  (setq str (propertize str 'face (vline-face visual-p))))
			(move-overlay ovr (point) (1+ (point)))
			(overlay-put ovr 'invisible t)
			(overlay-put ovr 'after-string str))))
		   (face-p
		    (move-overlay ovr (point) (1+ (point)))
		    (overlay-put ovr 'face (vline-face visual-p))))))))
	    (setq i (1+ i))
	    (vline-forward -1)))))))

(provide 'vline)

;;; Local Variables:
;;; time-stamp-format: "%:y-%02m-%02d %02H:%02M:%02S %Z %u"
;;; time-stamp-line-limit: 16
;;; End:

;;; vline.el ends here
