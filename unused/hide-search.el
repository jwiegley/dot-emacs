;; hide-search.el --- Search a buffer for lines to hide.

;; Copyright (C) 2000 Free Software Foundation, Inc.

;; Emacs Lisp Archive Entry
;; Author: Matteo Ianeselli <matteoianeselli@poboxes.com>
;; Created: 19 Sep 2000
;; Version: 1.0
;; Keywords: buffer, convenience

;; This file is not currently part of GNU Emacs.

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program ; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; hide-search.el provides three new commands to Emacs for hiding
;; lines:
;;
;; * hide-search: hide all the lines of text containing the given
;;                string. Hidden lines are shown as ellipses
;;                (``...'').
;;
;; * hide-search-regexp: like hide-search, but hides all the lines
;;                       matching a regular expression.
;;
;; * hide-search-show-all: show all lines hidden by hide-search or
;;                         hide-search-regexp. This is also the
;;                         behaviour when hide-search or
;;                         hide-search-regexp are given an empty
;;                         argument.
;;
;; To install it, just place this file somewhere in your load-path,
;; and then put (require 'hide-search) in your .emacs

;;; Code:

(defun hide-search-make-invisible (start end)
  "Make invisible the characters between START and END.
START and END are positions.
Invisibility is obtained using an overlay."
  (let ((overlay (make-overlay start end)))
    (overlay-put overlay 'invisible 'hide-search)
    (overlay-put overlay 'intangible t)))

(defun hide-search-show-all ()
  "Make visible all areas hidden using the hide-search commands."
  (interactive)
  (let ((overlays (overlays-in (point-min) (point-max)))
	i)
    (while (setq i (car overlays))
      (if (eq (overlay-get i 'invisible) 'hide-search)
	  (delete-overlay i))
      (setq overlays (cdr overlays)))))

(defun hide-search-setup-buffer ()
  (add-to-invisibility-spec '(hide-search . t))
  (make-local-variable 'line-move-ignore-invisible)
  (setq line-move-ignore-invisible t))


(defun hide-search (searchitem)
  "Hide the lines containing the specified string.
If SEARCHITEM is empty, show all lines, like with hide-search-show-all."
  (interactive "sHide lines containing: ")
  (if (string-equal searchitem "")
      (hide-search-show-all)
    (save-excursion
      (let ((range-end -1)
	    range-start)
	(hide-search-setup-buffer)
	(beginning-of-buffer)
	(while (search-forward searchitem nil t)
	  (if (= range-end (1- (line-beginning-position)))
	      (setq range-end (line-end-position))
	    (if range-start
		(hide-search-make-invisible range-start range-end))
	    (setq range-start (line-beginning-position)
		  range-end (line-end-position))))
	;; Last run...
	(if range-start
	    (hide-search-make-invisible range-start range-end))))))

(defun hide-search-regexp (searchitem)
  "Hide the lines matching the specified regexp.
If SEARCHITEM is empty, show all lines, like with hide-search-show-all."
  (interactive "sHide lines matching regexp: ")
  (if (string-equal searchitem "")
      (hide-search-show-all)
    (save-excursion
      (let ((range-end -1)
	    range-start)
	(hide-search-setup-buffer)
	(beginning-of-buffer)
	(while (search-forward-regexp searchitem nil t)

	  (if (= range-end (1- (line-beginning-position)))
	      (setq range-end (line-end-position))

	    (if range-start
		(hide-search-make-invisible range-start range-end))
	    (setq range-start (line-beginning-position)
		  range-end (line-end-position))))
	;; Last run...
	(if range-start
	    (hide-search-make-invisible range-start range-end))))))


(provide 'hide-search)
