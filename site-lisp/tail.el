;;; tail.el --- Tail files within Emacs

;; Copyright (C) 2000 by Benjamin Drieu

;; Author: Benjamin Drieu <bdrieu@april.org>
;; Keywords: tools

;; This file is NOT part of GNU Emacs.

;; This program as GNU Emacs are free software; you can redistribute
;; them and/or modify them under the terms of the GNU General Public
;; License as published by the Free Software Foundation; either
;; version 2, or (at your option) any later version.

;; They are distributed in the hope that they will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with them; see the file COPYING.  If not, write to the Free
;; Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
;; 02111-1307, USA.

;;  $Id: tail.el,v 1.1.1.1 2002/07/01 17:04:37 benj Exp $

;;; Commentary:

;;  This program displays ``tailed'' contents of files inside
;;  transients windows of Emacs.  It is primarily meant to keep an eye
;;  on logs within Emacs instead of using additional terminals.

;;  This was developed for GNU Emacs 20.x but should work as well for
;;  XEmacs 21.x

;;  Primary URL for tail.el is http://inferno.cs.univ-paris8.fr/~drieu/emacs/


;;; Code:

;;  Custom variables (may be set by the user)

(defgroup tail nil
  "Tail files or commands into Emacs buffers."
  :prefix "tail-"
  :group 'environment)

(defcustom tail-volatile t
  "Use non-nil to erase previous output"
  :options '(nil t)
  :group 'tail)

(defcustom tail-audible nil
  "Use non-nil to produce a bell when some output is displayed"
  :options '(nil t)
  :group 'tail)

(defcustom tail-raise nil
  "Use non-nil to raise current frame when some output is displayed (could be *very* annoying)"
  :options '(nil t)
  :group 'tail)

(defcustom tail-hide-delay 5
  "Time in seconds before a tail window is deleted"
  :type 'integer
  :group 'tail)

(defcustom tail-max-size 5
  "Maximum size of the window"
  :type 'integer
  :group 'tail)


;; Functions

;; Taken from calendar/appt.el
(defun tail-disp-window( tail-buffer tail-msg )
  "Display some content specified by ``tail-msg'' inside buffer
``tail-msg''.  Create this buffer if necessary and put it inside a
newly created window on the lowest side of the frame."

  (require 'electric)

  ;; Make sure we're not in the minibuffer
  ;; before splitting the window.

  (if (window-minibuffer-p)
      (other-frame -1))


  (let* ((this-buffer (current-buffer))
	 (this-window (selected-window))
	 (tail-disp-buf (set-buffer (get-buffer-create tail-buffer))))

    (if (cdr (assq 'unsplittable (frame-parameters)))
        ;; In an unsplittable frame, use something somewhere else.
        (display-buffer tail-disp-buf)
      (unless (or (special-display-p (buffer-name tail-disp-buf))
                  (same-window-p (buffer-name tail-disp-buf))
                  (get-buffer-window tail-buffer))

        ;; By default, split the bottom window and use the lower part.
        (tail-select-lowest-window)

        (if (not (window-minibuffer-p))
            (split-window))
	(pop-to-buffer tail-disp-buf))

      (toggle-read-only 0)
      (if tail-volatile
	  (erase-buffer))
      (insert-string tail-msg)
      (toggle-read-only 1)
      (shrink-window-if-larger-than-buffer (get-buffer-window tail-disp-buf t))
      (if (> (window-height (get-buffer-window tail-disp-buf t)) tail-max-size)
	  (shrink-window (- (window-height (get-buffer-window tail-disp-buf t)) tail-max-size)))
      (set-buffer-modified-p nil)
      (if tail-raise
	  (raise-frame (selected-frame)))
      (select-window this-window)
      (if tail-audible
	  (beep 1))
      (if tail-hide-delay
	  (run-with-timer tail-hide-delay nil 'tail-hide-window tail-buffer)))))


(defun tail-hide-window (buffer)
  (delete-window (get-buffer-window buffer t)))	; TODO: cancel timer when some output comes during that time


(defun tail-select-lowest-window ()
  "Select the lowest window on the frame."
  (let* ((lowest-window (selected-window))
	 (bottom-edge (car (cdr (cdr (cdr (window-edges))))))
         (last-window (previous-window))
         (window-search t))
    (while window-search
      (let* ((this-window (next-window))
	     (next-bottom-edge (car (cdr (cdr (cdr
					       (window-edges this-window)))))))
	(if (< bottom-edge next-bottom-edge)
	    (progn
	      (setq bottom-edge next-bottom-edge)
	      (setq lowest-window this-window)))

	(select-window this-window)
	(if (eq last-window this-window)
	    (progn
	      (select-window lowest-window)
	      (setq window-search nil)))))))


(defun tail-file (file)
  "Tails file specified with argument ``file'' inside a new buffer.
``file'' *cannot* be a remote file specified with ange-ftp syntaxm
because it is passed to the Unix tail command."
  (interactive "Ftail file: ")
  (tail-command "tail" "-f" file))	; TODO: what if file is remote (i.e. via ange-ftp)


(defun tail-command (command &rest args)
  "Tails command specified with argument ``command'', with arguments
``args'' inside a new buffer.  It is also called by tail-file"
  (interactive "sTail command: \neToto: ")
  (let ((process
	 (apply 'start-process-shell-command
		command
		(concat "*Tail: "
			command
			(if args " " "")
			(mapconcat 'identity args " ")
			"*")
		command
		args)))
    (set-process-filter process 'tail-filter)))


(defun tail-filter (process line)
  "Tail filter called when some output comes."
  (tail-disp-window (process-buffer process) line))


(provide 'tail)

;;; tail.el ends here
