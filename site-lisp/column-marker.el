;;; column-marker.el --- Highlight certain character columns
;; 
;; Filename: column-marker.el
;; Description: Highlight certain character columns
;; Author: Rick Bielawski <rbielaws@i1.net>
;; Maintainer: Rick Bielawski <rbielaws@i1.net>
;; Created: Tue Nov 22 10:26:03 2005
;; Version: 
;; Last-Updated: Fri Aug 18 17:42:04 2006 (-25200 Pacific Daylight Time)
;;           By: dradams
;;     Update #: 270
;; Keywords: tools convenience highlight
;; Compatibility: GNU Emacs 21, GNU Emacs 22
;; 
;; Features that might be required by this library:
;;
;;   None
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Commentary: 
;; 
;; Highlights the background at a given character column.
;; 
;; Commands `column-marker-1', `column-marker-2', and
;; `column-marker-3' each highlight a given column (using different
;; background colors, by default).
;;
;; - With no prefix argument, each highlights the current column
;;   (where the cursor is).
;;
;; - With a non-negative numeric prefix argument, each highlights that
;;   column.
;;
;; - With plain `C-u' (no number), each turns off its highlighting.
;;
;; - With `C-u C-u', each turns off all column highlighting.
;;
;; If two commands highlight the same column, the last-issued
;; highlighting command shadows the other - only the last-issued
;; highlighting is seen.  If that "topmost" highlighting is then
;; turned off, the other highlighting for that column then shows
;; through.
;;
;; Examples:
;;
;; M-x column-marker-1 highlights the column where the cursor is, in
;; `column-marker-1-face'.
;;
;; C-u 70 M-x column-marker-2 highlights column 70 in
;; `column-marker-2-face'.
;;
;; C-u 70 M-x column-marker-3 highlights column 70 in
;; `column-marker-3-face'.  The `column-marker-2-face' highlighting no
;; longer shows.
;;
;; C-u M-x column-marker-3 turns off highlighting for column-marker-3,
;; so `column-marker-2-face' highlighting shows again for column 70.
;;
;; C-u C-u M-x column-marker-1 (or -2 or -3) erases all column highlighting.
;;
;; These commands use `font-lock-fontify-buffer', so syntax
;; highlighting (`font-lock-mode') must be turned on.  There might be
;; a performance impact during refontification.
;;
;;
;; Installation: Place this file on your load path, and put this in
;; your init file (`.emacs'):
;;
;; (require 'column-marker)
;;
;; Other init file suggestions (examples):
;;
;; ;; Highlight column 80 in foo mode.
;; (add-hook foo-mode-hook (lambda () (interactive) (column-marker-1 80)))
;;
;; ;; Use `C-c m' interactively to highlight with `column-marker-1-face'.
;; (global-set-key [?\C-c ?m] 'column-marker-1)
;;
;;
;; Please report any bugs!
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Change log:
;; 
;; 2006/08/18 dadams
;;     column-marker-create: Add newlines to doc-string sentences.
;; 2005/12/31 dadams
;;     column-marker-create: Add marker to column-marker-vars inside the defun,
;;       so it is done in the right buffer, updating column-marker-vars buffer-locally.
;;     column-marker-find: Corrected comment.  Changed or to progn for clarity.
;; 2005/12/29 dadams
;;     Updated wrt new version of column-marker.el (mulit-column characters).
;;     Corrected stray occurrences of column-marker-here to column-marker-1.
;;     column-marker-vars: Added make-local-variable.
;;     column-marker-create: Changed positive to non-negative.
;;     column-marker-internal: Turn off marker when col is negative, not < 1.
;; 2005-12-29 RGB
;;     column-marker.el now supports multi-column characters.
;; 2005/11/21 dadams
;;     Combined static and dynamic. 
;;     Use separate faces for each marker.  Different interactive spec.
;; 2005/10/19 RGB
;;     Initial release of column-marker.el.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Code:

;;;;;;;;;;;;;;;;;;;;;;


(defvar column-marker-1-face 'column-marker-1-face
    "Face used for a column marker.  Usually a background color.
Changing this directly affects only new markers.")

(defface column-marker-1-face '((t (:background "gray")))
  "Face used for a column marker.  Usually a background color."
  :group 'faces)

(defvar column-marker-2-face 'column-marker-2-face
    "Face used for a column marker.  Usually a background color.
Changing this directly affects only new markers." )

(defface column-marker-2-face '((t (:background "cyan3")))
  "Face used for a column marker.  Usually a background color."
  :group 'faces)

(defvar column-marker-3-face 'column-marker-3-face
    "Face used for a column marker.  Usually a background color.
Changing this directly affects only new markers." )

(defface column-marker-3-face '((t (:background "orchid3")))
  "Face used for a column marker.  Usually a background color."
  :group 'faces)

(defvar column-marker-vars nil
  "List of all internal column-marker variables")
(make-variable-buffer-local 'column-marker-vars) ; Buffer local in all buffers.

(defmacro column-marker-create (var &optional face)
  "Define a column marker named %%colmark%%-VAR."
  (setq face (or face 'column-marker-1-face))
  `(progn
     ;; define context variable ,VAR so marker can be removed if desired
     (defvar ,var ()
       "Buffer local. Used internally to store column marker spec.")
     ;; context must be buffer local since font-lock is 
     (make-variable-buffer-local ',var)
     ;; Define wrapper function named ,VAR to call `column-marker-internal'
     (defun ,var (arg)
       ,(concat "Highlight column with face `" (symbol-name face)
                "'.\nWith no prefix argument, highlight current column.\n"
                "With non-negative numeric prefix arg, highlight that column number.\n"
                "With plain `C-u' (no number), turn off this column marker.\n"
                "With `C-u C-u' or negative prefix arg, turn off all column-marker highlighting.")
       (interactive "P")
       (unless (memq ',var column-marker-vars) (push ',var column-marker-vars))
       (cond ((null arg)          ; Default: highlight current column.
              (column-marker-internal ',var (1+ (current-column)) ,face))
             ((consp arg)
              (if (= 4 (car arg))
                  (column-marker-internal ',var nil) ; `C-u': Remove this column highlighting.
                (dolist (var column-marker-vars)
                  (column-marker-internal var nil)))) ; `C-u C-u': Remove all column highlighting.
             ((and (integerp arg) (>= arg 0)) ; `C-u 70': Highlight that column.
              (column-marker-internal ',var (1+ (prefix-numeric-value arg)) ,face))
             (t           ; `C-u -40': Remove all column highlighting.
              (dolist (var column-marker-vars)
                (column-marker-internal var nil)))))))

(defun column-marker-find (col)
  "Creates a function to locate a character in column COL."
  `(lambda (end)
     (let* ((start (point)))
       (when (> end (point-max)) (setq end (point-max)))

       ;; Try to keep `move-to-column' from going backward, though it still can.
       (unless (< (current-column) ,col) (forward-line 1))

       ;; Again, don't go backward.  Try to move to correct column.
       (when (< (current-column) ,col) (move-to-column ,col))

       ;; If not at target column, try to move to it.
       (while (and (< (current-column) ,col) (< (point) end)
                   (= 0 (+ (forward-line 1) (current-column)))) ; Should be bol.
         (move-to-column ,col))

       ;; If at target column, not past end, and not prior to start,
       ;; then set match data and return t.  Otherwise go to start
       ;; and return nil.
       (if (and (= ,col (current-column)) (<= (point) end) (> (point) start))
           (progn (set-match-data (list (1- (point)) (point))) t) ; Return t.
         (goto-char start) nil))))      ; Return nil.

(defun column-marker-internal (sym col &optional face)
  "SYM is the symbol for holding the column marker context.
COL is the column in which a marker should be set.
FACE is the face to use for the marker.
Supplying nil or 0 for COL turns off the marker."
  (setq face (or face 'column-marker-1-face))
  (when (symbol-value sym)   ; Remove any previously set column marker
    (font-lock-remove-keywords nil (symbol-value sym))
    (set sym nil))
  (when (or (listp col) (< col 0)) (setq col nil)) ; Allow nonsense stuff to turn off the marker
  (when col                             ; Generate a new column marker
    (set sym `((,(column-marker-find col) (0 ,face prepend t))))
    (font-lock-add-keywords nil (symbol-value sym) t))
  (font-lock-fontify-buffer))

;; If you need more markers you can create your own similarly.
;; All markers can be in use at once, and each is buffer-local,
;; so there is no good reason to define more unless you need more
;; markers in a single buffer.
(column-marker-create column-marker-1 column-marker-1-face)
(column-marker-create column-marker-2 column-marker-2-face)
(column-marker-create column-marker-3 column-marker-3-face)

;;;###autoload
(autoload 'column-marker-1 "column-marker" "Highlight a column." t)

;;;;;;;;;;;;;;;;;;

(provide 'column-marker)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; column-marker.el ends here
