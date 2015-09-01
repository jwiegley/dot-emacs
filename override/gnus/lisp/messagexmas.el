;;; messagexmas.el --- XEmacs extensions to message

;; Copyright (C) 1996-2014 Free Software Foundation, Inc.

;; Author: Lars Magne Ingebrigtsen <larsi@gnus.org>
;; Keywords: mail, news

;; This file is part of GNU Emacs.

;; GNU Emacs is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.	 See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;; Code:

(eval-when-compile (require 'cl))
(require 'nnheader)

(defvar message-xmas-dont-activate-region t
  "If t, don't activate region after yanking.")

(defvar message-xmas-glyph-directory nil
  "*Directory where Message logos and icons are located.
If this variable is nil, Message will try to locate the directory
automatically.")

(defvar message-use-toolbar (if (featurep 'toolbar) 'default)
  "*Position to display the toolbar.  Nil means do not use a toolbar.
If it is non-nil, it should be one of the symbols `default', `top',
`bottom', `right', and `left'.  `default' means to use the default
toolbar, the rest mean to display the toolbar on the place which those
names show.")

(defvar message-toolbar-thickness
  (if (featurep 'toolbar)
      (cons (specifier-instance default-toolbar-height)
	    (specifier-instance default-toolbar-width)))
  "*Cons of the height and the width specifying the thickness of a toolbar.
The height is used for the toolbar displayed on the top or the bottom,
the width is used for the toolbar displayed on the right or the left.")

(defvar message-toolbar
  '([message-spell ispell-message t "Spell"]
    [message-help (Info-goto-node "(Message)Top") t "Message help"])
  "The message buffer toolbar.")

(defun message-xmas-find-glyph-directory (&optional package)
  (setq package (or package "message"))
  (let ((dir (symbol-value
	      (intern-soft (concat package "-xmas-glyph-directory")))))
    (if (and (stringp dir) (file-directory-p dir))
	dir
      (nnheader-find-etc-directory package))))

(defun message-xmas-setup-toolbar (bar &optional force package)
  (let ((dir (or (message-xmas-find-glyph-directory package)
		 (message-xmas-find-glyph-directory "gnus")))
	(xpm (if (featurep 'xpm) "xpm" "xbm"))
	icon up down disabled name)
    (unless package
      (setq message-xmas-glyph-directory dir))
    (when dir
      (while bar
	(setq icon (aref (car bar) 0)
	      name (symbol-name icon)
	      bar (cdr bar))
	(when (or force
		  (not (boundp icon)))
	  (setq up (concat dir name "-up." xpm))
	  (setq down (concat dir name "-down." xpm))
	  (setq disabled (concat dir name "-disabled." xpm))
	  (if (not (file-exists-p up))
	      (setq bar nil
		    dir nil)
	    (set icon (toolbar-make-button-list
		       up (and (file-exists-p down) down)
		       (and (file-exists-p disabled) disabled)))))))
    dir))

(defun message-setup-toolbar ()
  (when (featurep 'toolbar)
    (if (and message-use-toolbar
	     (message-xmas-setup-toolbar message-toolbar))
	(let ((bar (or (intern-soft (format "%s-toolbar" message-use-toolbar))
		       'default-toolbar))
	      (height (car message-toolbar-thickness))
	      (width (cdr message-toolbar-thickness))
	      (cur (current-buffer))
	      bars)
	  (set-specifier (symbol-value bar) message-toolbar cur)
	  (set-specifier default-toolbar-height height cur)
	  (set-specifier default-toolbar-width width cur)
	  (set-specifier top-toolbar-height height cur)
	  (set-specifier bottom-toolbar-height height cur)
	  (set-specifier right-toolbar-width width cur)
	  (set-specifier left-toolbar-width width cur)
	  (if (eq bar 'default-toolbar)
	      (progn
		(remove-specifier default-toolbar-visible-p cur)
		(remove-specifier top-toolbar cur)
		(remove-specifier top-toolbar-visible-p cur)
		(remove-specifier bottom-toolbar cur)
		(remove-specifier bottom-toolbar-visible-p cur)
		(remove-specifier right-toolbar cur)
		(remove-specifier right-toolbar-visible-p cur)
		(remove-specifier left-toolbar cur)
		(remove-specifier left-toolbar-visible-p cur))
	    (set-specifier (symbol-value (intern (format "%s-visible-p" bar)))
			   t cur)
	    (setq bars (delq bar (list 'default-toolbar
				       'bottom-toolbar 'top-toolbar
				       'right-toolbar 'left-toolbar)))
	    (while bars
	      (set-specifier (symbol-value (intern (format "%s-visible-p"
							   (pop bars))))
			     nil cur))))
      (let ((cur (current-buffer)))
	(set-specifier default-toolbar-visible-p nil cur)
	(set-specifier top-toolbar-visible-p nil cur)
	(set-specifier bottom-toolbar-visible-p nil cur)
	(set-specifier right-toolbar-visible-p nil cur)
	(set-specifier left-toolbar-visible-p nil cur)))))

(defun message-xmas-exchange-point-and-mark ()
  "Exchange point and mark, but allow for XEmacs's optional argument."
  (exchange-point-and-mark message-xmas-dont-activate-region))

(defun message-xmas-maybe-fontify ()
  (when (featurep 'font-lock)
    (font-lock-set-defaults)))

(defun message-xmas-make-caesar-translation-table (n)
  "Create a rot table with offset N."
  (let ((i -1)
	(table (make-string 256 0))
	(a (mm-char-int ?a))
	(A (mm-char-int ?A)))
    (while (< (incf i) 256)
      (aset table i i))
    (concat
     (substring table 0 A)
     (substring table (+ A n) (+ A n (- 26 n)))
     (substring table A (+ A n))
     (substring table (+ A 26) a)
     (substring table (+ a n) (+ a n (- 26 n)))
     (substring table a (+ a n))
     (substring table (+ a 26) 255))))

(defun message-xmas-make-date (&optional now)
  "Make a valid data header.
If NOW, use that time instead."
  (let ((zone (car (current-time-zone)))
	sign)
    (if (>= zone 0)
	(setq sign "+")
      (setq sign "-"
	    zone (- zone)))
    (format "%s %s%02d%02d"
	    (format-time-string "%a, %d %b %Y %T" now)
	    sign
	    (/ zone 3600)
	    (/ (% zone 3600) 60))))

(add-hook 'message-mode-hook 'message-xmas-maybe-fontify)

(defun message-xmas-redefine ()
  "Redefine message functions for XEmacs."
  (defalias 'message-exchange-point-and-mark
    'message-xmas-exchange-point-and-mark)
  (defalias 'message-mark-active-p
    'region-exists-p)
  (defalias 'message-make-caesar-translation-table
    'message-xmas-make-caesar-translation-table)
  (defalias 'message-make-overlay 'make-extent)
  (defalias 'message-delete-overlay 'delete-extent)
  (defalias 'message-overlay-put 'set-extent-property)
  (defalias 'message-make-date 'message-xmas-make-date))

(message-xmas-redefine)

(provide 'messagexmas)

;;; messagexmas.el ends here
