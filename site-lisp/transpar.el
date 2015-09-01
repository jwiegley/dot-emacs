;;; transpar.el --- Transpose paragraph text as a table.
;; 
;; Filename: transpar.el
;; Description: Transpose paragraph text as a table.
;; Author: Mark Armstrong
;; Maintainer: Mark Armstrong
;; Copyright (C) 2012, Mark Armstrong, all rights reserved.
;; Created: Tue Jun 19 13:29:00 2012 (-0700)
;; Version: 1.0
;; Last-Updated: Tue Jun 19 13:44:18 2012 (-0700)
;;           By: dradams
;;     Update #: 18
;; URL: http://www.emacswiki.org/cgi-bin/wiki/transpar.el
;; Keywords: table column rectangle matrix
;; Compatibility: GNU Emacs 22.x, GNU Emacs 23.x, GNU Emacs 24.x
;; 
;; Features that might be required by this library:
;;
;;   None
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Commentary:
;;
;;  I frequently edit big space-separated text tables.  The hardest
;;  thing to to in emacs is edit table columns, as most emacs commands
;;  operate most efficiently in a line-oriented nature.
;;
;;  I have tried to use the various other modes and functions for
;;  aligning text and working with tables as found in this wiki, but
;;  they really bog down when tables get big (hundreds or thousands of
;;  rows and columns) for one or more of the following reasons:
;;
;;  * most are regexp-based, which is slower than using split-string
;;
;;  * some want you to enter the dimensions of the table, which I
;;    never know exactly
;;
;;  * some mark up the table view with lines and separators, which I
;;    don't want
;;
;;  * some want to store the file with metadata in it, whereas I just
;;    want the bare text in the saved file
;;
;;  * some make you learn a whole new set of navigation keys and won't
;;    let you just edit the table
;;
;;  In contrast, I find that a simple transpose and align function
;;  allows emacs to function well as a table editor even in basic text
;;  mode.  Most importantly, once a table has been transposed, the
;;  powerful line-oriented editing commands can now operate
;;  effectively on columns.  Also, once the table has been aligned,
;;  even the builtin rectangle edit commands become more useful for
;;  editing columns.
;;
;;  The below command will act upon the paragraph containing the point
;;  in any text document.  It will interpret that paragraph as a text
;;  table by splitting the lines using the split-string function.  It
;;  will then replace that paragraph with its transpose with columns
;;  left-aligned.  Column widths are determined by the maximum element
;;  size in each column.  If the table is not rectangular then missing
;;  elements are replaced with ".".
;;
;;  I find no need for a separate align-only command since that can be
;;  achieved simply by transposing twice.
;;
;;  Example:
;;
;;  <pre>
;;  a bbbb c       a    1 4
;;  1 2       -->  bbbb 2 5
;;  4 5 6          c    . 6
;;  </pre>
;;
;;  To use:
;;
;;  1. Put this file in your `load-path'.
;;  2. Put this in your init file (~/.emacs): (require 'transpar)
;;  3. Bind `transpose-paragraph-as-table' to a key, if you like.
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Change Log:
;;
;; 2012/06/19 dadams
;;     Created from first post on Emacs Wiki, 2012-06-19.
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 3, or
;; (at your option) any later version.
;; 
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;; 
;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Code:

(defun transpose-paragraph-as-table ()
  "Transpose and align current paragraph."
  (interactive)
  (transpose-region-as-table (paragraph-beginning-position) (paragraph-end-position)))

(defun transpose-region-as-table (beg end)
  "Transpose and align region."
  (goto-char beg)
  (insert (list-to-text (align-list (transpose-list (text-to-list (delete-and-extract-region beg end))))))
  (goto-char beg))

(defun list-to-text (arg)
  "List to text.  Join with space and then with newline."
  (mapconcat 'identity (mapcar '(lambda (row) (mapconcat 'identity row " ")) arg) "\n"))

(defun text-to-list (arg)
  "Text to list.  Separate by newline then by whitespace."
  (mapcar '(lambda (row) (split-string row split-string-default-separators t)) (split-string arg "\n")))

(defun transpose-list (rowlist)
  "Transpose list.  Missing elements marked with periods."
  (let (newlist collist)
    (dotimes (col (apply 'max (mapcar 'length rowlist)))
      (setq collist ())
      (dolist (row rowlist)
        (if (< col (length row))
            (push (nth col row) collist)
          (push "." collist)))
      (push (reverse collist) newlist))
    (reverse newlist)))

(defun align-list (rowlist)
  "Align list.  Determine column widths from max element size."
  (let (widlist newlist collist)
    (dotimes (col (apply 'max (mapcar 'length rowlist)))
      (push (apply 'max (mapcar '(lambda (row) (length (nth col row))) rowlist)) widlist))
    (setq widlist (reverse widlist))
    (dolist (row rowlist)
      (setq collist ())
      (dotimes (col (length row))
        (push (format (concat "%-" (number-to-string (nth col widlist)) "s") (nth col row)) collist))
      (push (reverse collist) newlist))
    (reverse newlist)))

(defun paragraph-beginning-position ()
  "Paragraph beginning position."
  (save-excursion (forward-paragraph) (backward-paragraph) (forward-word) (line-beginning-position)))

(defun paragraph-end-position ()
  "Paragraph end position."
  (save-excursion (forward-paragraph) (backward-word) (line-end-position)))

;;;;;;;;;;;;;;;;;;;;;;;

(provide 'transpar)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; transpar.el ends here
