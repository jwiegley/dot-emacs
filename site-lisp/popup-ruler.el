;;; popup-ruler.el --- Displays a ruler at point.

;; Copyright (C) 2005 Free Software Foundation, Inc.

;; Author: Rick Bielawski <rbielaws@i1.net>
;; Keywords: tools convenience
;; Maintainer: Rick Bielawski <rbielaws@i1.net>

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING. If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; Displays a ruler at (point) for measuring and positioning text.
;;
;; Three different rulers can be displayed depending on prefix arg.
;; One measures from the left most column, one from point and one
;; reaches over a delimiter such as quotes to measure text within.

;; (load "popup-ruler") and see the help strings for
;; `popup-ruler' and `popup-ruler-vertical'

;; This ruler was inspired by the one in fortran-mode but code-wise
;; bears no resemblance.

;;; Installation:

;; Put popup-ruler.el on your load path, add a load command to .emacs and
;; map the main routines to convenient keystrokes.  For example:

;; (require 'popup-ruler)
;; (global-set-key [f9]    'popup-ruler)
;; (global-set-key [S-f9]  'popup-ruler-vertical)

;; Please report any bugs!

;;; ToDo:

;; Handling lines that wrap. i.e. when truncate-lines is nil.

;;; History:

;; 2005-10-09 RGB Initial packaged release.
;; 2005-10-23 RGB Added initial attempt at a vertical ruler.
;; 2005-10-25 RGB Make vertical ruler numbering interval customizable
;; 2005-10-26 RGB Patch bug causing ruler to stay in your buffer
;;                with no undo history to get rid of it.
;; 2005-11-18 RGB Removed workaround patch of undo problem.
;;                Replaced it with a more robust solution.
;;                Improved cursor position during vertical ruler.
;; 2006-06-28 RGB Minor update to comments.
;; 2006-06-28 RGB Changed popup-ruler-momentary-column to work the new way
;;                that momentary-string-display does, using overlays.
;;; Code:

(defgroup popup-ruler nil
  "Major mode for editing Tandem DDL source files in Emacs."
  :group 'convenience
)

;;;###autoload
(defun popup-ruler (arg)
  "Temporarily display a ruler with `momentary' face above the current line.
With \\[universal-argument] prefix argument, make the ruler measure in both
directions from point.  Use \\[universal-argument] \\[universal-argument] for
quoted text.  The ruler then skips the quote character when measuring."
  (interactive "P")
  (momentary-string-display
   (cond
    ((null arg)
     ;; The original left to right ruler
     (let* ((right-len (+ (window-hscroll)(window-width) -1))
            (right (popup-ruler-l-r right-len)))
       (concat (cadr right) "\n"
               (car right) "\n")))
    ((if (listp arg) (< 4 (car arg))(= 0 arg))
     ;; String ruler.  Measures both directions skipping 1 char.
     (let* ((left-len (1- (current-column)))
            (right-len (- (+ (window-hscroll)(window-width)) 3 left-len))
            (left (popup-ruler-r-l left-len))
            (right (popup-ruler-l-r right-len)))
       (concat (cadr left) (make-string 2 ? ) (cadr right) "\n"
               (car left) (make-string 2 ? ) (car right) "\n")))
    ;; Measures both directions from point
    (t (let* ((left-len (current-column))
              (right-len (- (+ (window-hscroll)(window-width)) 1 left-len))
              (left (popup-ruler-r-l left-len))
              (right (popup-ruler-l-r right-len)))
         (concat (cadr left) (cadr right) "\n"
                 (car left) (car right) "\n"))))
   (line-beginning-position)
   nil "[space] Clears ruler"))

(defcustom popup-ruler-vertical-interval 1
  "Puts numbers on a vertical ruler only at this interval.
1 is the default which means every line.  5 would mean every N mod 5 line.
Line number 1 is always marked explicitly regardless of this value."
  :group 'popup-ruler
)

;;;###autoload
(defun popup-ruler-vertical (arg)
  "Temporarily display a vertical ruler in the `current-column'.
With \\[universal-argument] prefix argument, make the ruler measure in both
directions from point.  Use \\[universal-argument] \\[universal-argument] to
make the ruler start at zero rather than one."
  (interactive "P")
  (popup-ruler-momentary-column
   (popup-ruler-strings
    (cond
     ;; The top of window to bottom ruler
     ((null arg) 'top-1)
     ;; Measures both directions from point starting at zero
     ((if (listp arg) (< 4 (car arg))(= 0 arg)) 'point-0)
     ;; Measures both directions from point starting at one
     (t 'point-1)))
   (current-column))(sit-for 0)(message nil))

(defun popup-ruler-r-l (len)
  "Returns right to left running ruler of length LEN.
  Result is a list of 2 strings, markers and counters."
  (let* ((iterations (/ (1- (abs len)) 10))
         (short (- (* 10 (1+ iterations)) (abs len)))
         (result1 "|....|...|")
         (result2 "10   5   1")
         (inc1    "|....|....")
         (inc2    "%d0         ")
         (i 1))
    (while  (<= i iterations)
      (setq i (1+ i))
      (setq result1 (concat inc1 result1))
      (setq result2 (concat (substring (format inc2 i) 0 10) result2)))
    (list (substring result1 short) (substring result2 short))))

(defun popup-ruler-l-r (len)
  "Returns left to right running ruler of length LEN.
  Result is a list of 2 strings; markers and counters."
  (let* ((iterations (/ (1- (abs len)) 10))
         (result1 "|...|....|")
         (result2 "1   5   10")
         (inc1    "....|....|")
         (inc2    "        %d0")
         (i 1))
    (while  (<= i iterations)
      (setq i (1+ i))
      (setq result1 (concat result1 inc1))
      (setq result2 (concat result2 (substring (format inc2 i) -10))))
    (list (substring result1 0 len) (substring result2 0 len))))

(defun popup-ruler-window-position (&optional visible)
  "Returns the cons (screen-line . screen-column) of point.
When VISIBLE is non-nil a screen-column of 0 is returned when a negative
value would otherwise be returned such as after (scroll-left).
nil is returned if current-buffer is not in the current window."
  (if (eq (current-buffer) (window-buffer))
      (if (or truncate-lines (/= 0 (window-hscroll)))
          ;; Lines never wrap when horizontal scrolling is in effect.
          (let ((window-column (- (current-column)(window-hscroll)))
                (window-line (count-lines (window-start)(point))))
            (cond
             ((= 0 (current-column))
              (cons window-line (if visible 0 window-column)))
             ((<= (current-column) (window-hscroll))
              (cons (1- window-line) (if visible 0 window-column)))
             (t (cons (1- window-line) window-column))))
        ;; When lines are not being truncated we deal with wrapping
        (let ((window-column (% (current-column)(window-width)))
              (window-line (count-screen-lines (window-start)(point))))
          (if (= 0 window-column)
              (cons window-line window-column)
            (cons (1- window-line) window-column))))))

(defun popup-ruler-strings ( type )
  "Return a list of strings that form a vertical ruler.
The ruler is intended to run from the top of the screen to the bottom so
there are (window-height) strings.  When counter originates at point or
mark the numbering increments in both directions from that line.  This
does not yet support generating strings for wrapped lines.

Supported types are:
    'top-1      Numbering starts at the top of the screen
    'bottom-1   Numbering starts at the bottom of the screen
    'point-1    The line containing point is number 1
    'point-0    The line containing point is number 0
    'mark-1     The line containing mark is numbered 1
    'mark-0     The line containing mark is numbered 0
"
  (if (or truncate-lines (/= 0 (window-hscroll)))
      (let* ((position (popup-ruler-window-position t))
             (row (car position))
             (col (cdr position))
             (start 1)
;           (mark-dist (if (mark)(count-lines (mark)(point)) 0))
;           (direction (if (= 0 mark-dist)(count-lines (mark)(point))0))
             (mid (1+ row))
             (end (1- (window-height)))
             (width (length (number-to-string (max start end mid))))
             ruler-list)
        (cond
         ((eq type 'top-1)
          (popup-ruler-make-strings
           start end popup-ruler-vertical-interval width))
         ((eq type 'bottom-1)
          (popup-ruler-make-strings
           end start popup-ruler-vertical-interval width))
         ((eq type 'point-1)
          (append (popup-ruler-make-strings
                   mid 1
                   popup-ruler-vertical-interval width)
                  (popup-ruler-make-strings
                   2 (1- end) popup-ruler-vertical-interval width)))
         ((eq type 'point-0)
          (append (popup-ruler-make-strings
                   (1- mid) 0 popup-ruler-vertical-interval width)
                  (popup-ruler-make-strings
                   1 (- end 2) popup-ruler-vertical-interval width)))
         ((eq type 'mark-1)
          (append (popup-ruler-make-strings
                   (1- mid) 0 popup-ruler-vertical-interval width)
                  (popup-ruler-make-strings
                   1 (- end 2) popup-ruler-vertical-interval width)))
         (t (error "popup-ruler-strings - unsupported type `%s'" type))))
    (error "popup-ruler-strings - unsupported window configuration")))

(defun popup-ruler-make-strings ( start end interval width )
  "Return a list of strings that form a vertical ruler.
Numbering of the strings runs from START thru END where strings not a
multiple of INTERVAL do not contain numbers.  The exception being that a
string numbered 1 is always numbered."
  (let* ((fmt (concat "|-%" (number-to-string width) "d-|"))
         (spacer (concat "|-" (make-string width ? ) "-|"))
         (increment (if (> start end) -1 1))
         (done nil)
         ruler-list)
    (while (not done)
      (if (or (= start 1) (= 0 (% start interval)))
          (push (format fmt start) ruler-list)
        (push spacer ruler-list))
      (setq done (= start end))
      (setq start (+ increment start)))
    (reverse ruler-list)))

(defun popup-ruler-momentary-column (string-list col)
  "Momentarily display STRING-LIST in the current buffer at COL.

The strings in STRING-LIST cannot contain \\n.
They are displayed in `momentary' face, which is customizable.

Starting at the top of the display each string in the list is displayed
on subsequent lines at column COL until one of the following is reached:
the last string in STRING-LIST, the bottom of the display, the last line
in the buffer.

Display remains until next event is input."
  (let ((count (window-height))
        (loc (count-lines (window-start)(point)))
        overlay-list
        this-overlay
        buffer-file-name)
    (goto-char (window-start))
    ;; although we now use overlays, temporary-invisible-change is still
    ;; needed because move-to-column can insert spaces into the buffer.
    (temporary-invisible-change
     (unwind-protect
         (progn
           (while (and string-list (> count 0))
             (move-to-column col t)
             (setq this-overlay (make-overlay (point) (point) nil t))
             (setq overlay-list (cons this-overlay overlay-list))
             (overlay-put this-overlay 'before-string
                          (propertize (pop string-list) 'face 'momentary))
             (forward-line)
             (if (< (point)(point-max))
                 (setq count (1- count))
               (setq count -1)))
           (goto-char (window-start))
           (if (= col 0)(forward-line loc)
             (forward-line (1- loc))
             (move-to-column col)) 
           (read-key-sequence-vector "Any event removes ruler.")())
       (while overlay-list
         (delete-overlay (prog1 (car overlay-list)
                           (setq overlay-list (cdr overlay-list)))))))))

(defmacro temporary-invisible-change (&rest forms)
  "Executes FORMS with a temporary buffer-undo-list, undoing on return.
The changes you make within FORMS are undone before returning.
But more importantly, the buffer's buffer-undo-list is not affected.
This macro allows you to temporarily modify read-only buffers too.
Always return nil"
`(let* ((buffer-undo-list)
          (modified (buffer-modified-p))
          (inhibit-read-only t))
     (save-excursion
       (unwind-protect
           (progn ,@forms)
         (primitive-undo (length buffer-undo-list) buffer-undo-list)
         (set-buffer-modified-p modified))) ()))

(provide 'popup-ruler)

;;; popup-ruler.el ends here.
