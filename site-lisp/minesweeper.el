;;; minesweeper.el --- play minesweeper in Emacs

;; Copyright 2010-2012, 2014 Zachary Kanfer

;; Author: Zachary Kanfer <zkanfer@gmail.com>
;; Version: 2012.07.02
;; URL: https://bitbucket.org/zck/minesweeper.el

;; This file is not part of GNU Emacs

;; This program is free software: you can redistribute it and/or modify
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

;; This program is an implementation of minesweeper for Emacs.

;; This game consists of a minefield.  There are squares with mines, and squares without mines.
;; The goal is to reveal all squares that do not have a mine.  If you reveal a mine, it explodes,
;; and the game is over!

;; To begin playing, call `M-x minesweeper`.

;; Use the arrow keys, p/b/n/f, or C-p/C-n/C-b/C-f to move around in the minefield.

;; To reveal squares, either left-click on them, or move point and press space, enter, or `x`.

;; When a square is revealed, if it is not a mine, there will be a number indicating the count of mines in the neighboring eight squares.
;; If a square with no neighboring mines is revealed, all its neighbors will also be revealed.

;; You can mark squares that you think have mines in them.  Marked squares are protected
;; from being revealed by any means.
;; To mark a square, right-click on it, or press `m`.  Marked squares can be unmarked the same way.

;; You can choose to reveal all the neighbors of a square by middle-clicking on a square, or moving point there and pressing `c`.

;; Keywords: game fun minesweeper inane diversion

;;; Code:

(require 'cl-lib)

(define-derived-mode minesweeper-mode special-mode "minesweeper-mode"
  (define-key minesweeper-mode-map (kbd "SPC") 'minesweeper-choose)
  (define-key minesweeper-mode-map (kbd "x") 'minesweeper-choose)
  (define-key minesweeper-mode-map (kbd "RET") 'minesweeper-choose)
  (define-key minesweeper-mode-map [mouse-1] 'minesweeper-choose)
  (define-key minesweeper-mode-map (kbd "m") 'minesweeper-toggle-mark)
  (define-key minesweeper-mode-map [mouse-3] 'minesweeper-toggle-mark-mouse)
  (define-key minesweeper-mode-map (kbd "C-b") 'minesweeper-backward-char)
  (define-key minesweeper-mode-map (kbd "b") 'minesweeper-backward-char)
  (define-key minesweeper-mode-map (kbd "C-f") 'minesweeper-forward-char)
  (define-key minesweeper-mode-map (kbd "f") 'minesweeper-forward-char)
  (define-key minesweeper-mode-map (kbd "C-n") 'minesweeper-next-line)
  (define-key minesweeper-mode-map (kbd "n") 'minesweeper-next-line)
  (define-key minesweeper-mode-map (kbd "p") 'previous-line)
  (define-key minesweeper-mode-map (kbd "C-p") 'previous-line)
  (define-key minesweeper-mode-map (kbd "a") 'move-beginning-of-line)
  (define-key minesweeper-mode-map (kbd "C-e") 'minesweeper-move-end-of-field)
  (define-key minesweeper-mode-map (kbd "e") 'minesweeper-move-end-of-field)
  (define-key minesweeper-mode-map (kbd "c") 'minesweeper-choose-around)
  (define-key minesweeper-mode-map [mouse-2] 'minesweeper-choose-around-mouse)
  (define-key minesweeper-mode-map (kbd "s") 'minesweeper-toggle-show-neighbors))

(defvar *minesweeper-idle-timer* nil
  "The timer used to highlight neighbors.")

(defvar *minesweeper-idle-delay* 0.0625
  "The time Emacs must be idle before highlighting the neigbors of point.")

;;;###autoload
(defun minesweeper () "Major mode for playing Minesweeper in Emacs.

There's a field of squares; each square may hold a mine.
Your goal is to uncover all the squares that don't have mines.
If a revealed square doesn't have a mine, you'll see how many mines
are in the eight neighboring squares.
You may mark squares, which protects them from accidentally being revealed.

\\{minesweeper-mode-map}"
  (interactive)
  (switch-to-buffer "minesweeper")
  (minesweeper-mode)
  (minesweeper-begin-game))

(defface minesweeper-blank
  '((t (:foreground "black"))) "face for blank spaces" :group 'minesweeper-faces)

(defface minesweeper-marked
  '((t (:foreground "black"))) "face for marked spaces" :group 'minesweeper-faces)

(defface minesweeper-0
  '((t (:foreground "Grey"))) "face for zero spaces" :group 'minesweeper-faces)

(defface minesweeper-1
  '((t (:foreground "#2020FF"))) "face for 1 spaces" :group 'minesweeper-faces)

(defface minesweeper-2
  '((t (:foreground "#00C000"))) "face for 2 spaces" :group 'minesweeper-faces)

(defface minesweeper-3
  '((t (:foreground "#6000A0"))) "face for 3 spaces" :group 'minesweeper-faces)

(defface minesweeper-4
  '((t (:foreground "#C00000"))) "face for 4 spaces" :group 'minesweeper-faces)

(defface minesweeper-5
  '((t (:foreground "#008080"))) "face for 5 spaces" :group 'minesweeper-faces)

(defface minesweeper-6
  '((t (:foreground "#FF8000"))) "face for 6 spaces" :group 'minesweeper-faces)

(defface minesweeper-7
  '((t (:foreground "#A06000"))) "face for 7 spaces" :group 'minesweeper-faces)

(defface minesweeper-8
  '((t (:foreground "#FF0000"))) "face for 8 spaces" :group 'minesweeper-faces)

(defface minesweeper-neighbor
  '((t (:background "#C0FFFF"))) "face for the neighbors of point" :group 'minesweeper-faces)

(defface minesweeper-explode
  '((t (:background "#FF0000"))) "face for a clicked-on mine" :group 'minesweeper-faces)

(defface minesweeper-mismarked
  '((t (:background "#888888"))) "face for mismarked mines, at end of game" :group 'minesweeper-faces)

(defvar *minesweeper-board-width* nil
  "The number of columns on the Minesweeper field.")

(defconst *minesweeper-default-width* 10
  "The default board width.")

(defvar *minesweeper-board-height* nil
  "The number of rows on the Minesweeper field.")

(defconst *minesweeper-default-height* 10
  "The default board height.")

(defvar *minesweeper-mines* nil
  "The number of mines on the Minesweeper field.")

(defconst *minesweeper-default-mines* 10
  "The default number of mines.")

(defvar *minesweeper-field* nil
  "The minefield itself.

If a mine is in the square, ?X is stored.
Otherwise, the number of mines in neighboring squares is stored.

This is a hashtable where the key is a list.  The first element
of the list is the row, and the second is the column.")

(defvar *minesweeper-reveals* nil
  "Holds 't in (row, col) if (row, col) has been revealed.")

(defvar *minesweeper-marks* nil
  "Holds 't in (row, col) iff (row, col) has been marked.  A marked square cannot be chosen.")

(defvar *minesweeper-blanks-left* 0
  "Holds the number of empty squares left.  After 'minesweeper-init has been called, the user will win the game when this becomes zero again.")

(defvar *minesweeper-debug* nil
  "When 't, print debugging information.")

(defvar *minesweeper-first-move* 't
  "If 't, the next move is the first move.  So if a mine is selected, move that mine elsewhere.")

(defvar *minesweeper-wins* 0
  "The number of times the player has won the game this session.")

(defvar *minesweeper-losses* 0
  "The number of times the player has lost the game this session.")

(defvar *minesweeper-game-epoch* nil
  "The time the current game started.")

(defvar *minesweeper-min-free-squares* 1
  "The minimum number of squares which must be free.")

(defvar *minesweeper-top-overlay*
  (let ((overlay (make-overlay 0 0)))
    (overlay-put overlay 'face 'minesweeper-neighbor)
    overlay)
  "The overlay to go above point.")

(defvar *minesweeper-left-overlay*
  (let ((overlay (make-overlay 0 0)))
    (overlay-put overlay 'face 'minesweeper-neighbor)
    overlay)
  "The overlay to go left of point.")

(defvar *minesweeper-right-overlay*
  (let ((overlay (make-overlay 0 0)))
    (overlay-put overlay 'face 'minesweeper-neighbor)
    overlay)
  "The overlay to go right of point.")

(defvar *minesweeper-bottom-overlay*
  (let ((overlay (make-overlay 0 0)))
    (overlay-put overlay 'face 'minesweeper-neighbor)
    overlay)
  "The overlay to go below point.")

(defvar *minesweeper-explode-overlay*
  (let ((overlay (make-overlay 0 0)))
    (overlay-put overlay 'face 'minesweeper-explode)
    overlay)
  "The overlay that marks the chosen square iff it was a mine.")

(defvar *minesweeper-mismarked-overlay*
  (let ((overlay (make-overlay 0 0)))
    (overlay-put overlay 'face 'minesweeper-mismarked)
    overlay)
  "The overlay used at end of game to highlight marked squares that aren't mines.")

(defvar *minesweeper-mark-count*
  0
  "The number of mines the user has marked.")

(defvar *minesweeper-faces*
  (let ((table (make-hash-table :test 'equal)))
    (puthash ?0 'minesweeper-0 table)
    (puthash ?1 'minesweeper-1 table)
    (puthash ?2 'minesweeper-2 table)
    (puthash ?3 'minesweeper-3 table)
    (puthash ?4 'minesweeper-4 table)
    (puthash ?5 'minesweeper-5 table)
    (puthash ?6 'minesweeper-6 table)
    (puthash ?7 'minesweeper-7 table)
    (puthash ?8 'minesweeper-8 table)
    (puthash ?- 'minesweeper-blank table)
    (puthash ?* 'minesweeper-marked table)
    table)
  "The hashtable mapping a character to the face it should have.")

(defvar *minesweeper-game-over* nil
  "'t if the user has selected a mine or selected all the empty squares, nil otherwise.")

(defmacro minesweeper-debug (&rest body)
  "If *minesweeper-debug* is 't, log ,@BODY as a string to the buffer named 'debug'."
  `(when *minesweeper-debug*
     (print (concat ,@body)
	    (get-buffer-create "debug"))))

(defun minesweeper-move-end-of-field ()
  "Move to the last cell in this row of the minefield."
  (interactive)
  (move-end-of-line nil)
  (backward-char))

(defun minesweeper-forward-char ()
  "Move to the next character, unless that move would take us to the end of the line."
  (interactive)
  (forward-char)
  (when (eolp)
    (backward-char)))

(defun minesweeper-backward-char ()
  "Move to the previous character, unless that move would take us to the previous line."
  (interactive)
  (unless (bolp)
    (backward-char)))

(defun minesweeper-next-line ()
  "Move to the next line in the minefield.

If point is already at the last line of the minefield, stay where it is."
  (interactive)
  (when (< (line-number-at-pos)
           *minesweeper-board-height*)
    (let ((column (current-column)));; flycheck bitches if you use next-line.
      (forward-line) ;; even though that gets rid of this boilerplate.
      (forward-char column))))

(defun minesweeper-begin-game (&optional width height mines)
  "Begin the game.

This prompts the user for the minefield size and number of mines.
Use WIDTH, HEIGHT, and MINES as the default values, but still prompt the user."
  (minesweeper-debug "beginning the game")
  (if (y-or-n-p (concat (number-to-string (or width *minesweeper-board-width* *minesweeper-default-width*))
			" by "
			(number-to-string (or height *minesweeper-board-height* *minesweeper-default-height*))
			" with "
			(number-to-string (or mines *minesweeper-mines* *minesweeper-default-mines*))
			" mines ok? "))
      (minesweeper-init (or width *minesweeper-board-width* *minesweeper-default-width*)
			(or height *minesweeper-board-height* *minesweeper-default-height*)
			(or mines *minesweeper-mines* *minesweeper-default-mines*))
    (let ((width (minesweeper-get-integer "Minefield width? " (number-to-string (or width *minesweeper-board-width* *minesweeper-default-width*))))
	  (height (minesweeper-get-integer "Minefield height? " (number-to-string (or height *minesweeper-board-height* *minesweeper-default-height*))))
	  (mines (minesweeper-get-integer "Number of mines? " (number-to-string (or mines *minesweeper-mines* *minesweeper-default-mines*)))))
      (minesweeper-init width height mines)))
  (minesweeper-print-field)
  (goto-char (+ (* (truncate (1- *minesweeper-board-height*)
                             2)
		   (1+ *minesweeper-board-width*))
		(ceiling (/ (float *minesweeper-board-width*) 2))))
  (when *minesweeper-idle-timer*
    (cancel-timer *minesweeper-idle-timer*)
    (setq *minesweeper-idle-timer* nil))
  (setq *minesweeper-idle-timer* (run-with-idle-timer *minesweeper-idle-delay*
						      t
						      'minesweeper-show-neighbors))
  (message "Good luck!"))

(defun minesweeper-init (&optional width height mines)
  "Begin a game of Minesweeper with a board that's size WIDTH by HEIGHT containing MINES mines."
  (minesweeper-debug "initializing the game")
  (setq *minesweeper-board-width* (or width *minesweeper-default-width*)
	*minesweeper-board-height* (or height *minesweeper-default-height*)
	*minesweeper-mines* (or mines *minesweeper-default-mines*)
	*minesweeper-field* (make-hash-table :test 'equal :size (* *minesweeper-board-width*
								   *minesweeper-board-height*))
	*minesweeper-reveals* (make-hash-table :test 'equal :size (* *minesweeper-board-width*
								     *minesweeper-board-height*))
	*minesweeper-marks* (make-hash-table :test 'equal :size (* *minesweeper-board-width*
								   *minesweeper-board-height*))
	*minesweeper-blanks-left* (- (* *minesweeper-board-width*
					*minesweeper-board-height*)
				     *minesweeper-mines*)
	*minesweeper-first-move* 't
	*minesweeper-game-epoch* nil
	*minesweeper-mark-count* 0
	*minesweeper-game-over* nil)
  (minesweeper-debug "most global vars set -- checking for overpopulation of mines.")
  (while (< *minesweeper-blanks-left* *minesweeper-min-free-squares*)
    (setq *minesweeper-mines* (minesweeper-get-integer (format "Too many mines. You can have at most %d mines. Number of mines?" (- (* *minesweeper-board-width*
																       *minesweeper-board-height*)
																    *minesweeper-min-free-squares*))
						       *minesweeper-default-mines*)
	  *minesweeper-blanks-left* (- (* *minesweeper-board-width*
					  *minesweeper-board-height*)
				       *minesweeper-mines*))))


(defun minesweeper-fill-field (protect-row protect-col)
  "Fill 'the field with mines, and build the neighbor count.

It will not place any mines in the square (PROTECT-ROW, PROTECT-COL)."
  (minesweeper-debug "filling the field")
  (dotimes (col *minesweeper-board-width*)
    (minesweeper-debug "inside outer loop -- col is " (number-to-string col))
    (dotimes (row *minesweeper-board-height*)
      (minesweeper-debug "inside inner loop -- setting up mine " (number-to-string col) " " (number-to-string row))
      (minesweeper-set-mine row col ?0)
      (minesweeper-hide row col)
      (minesweeper-unmark row col)))
  (minesweeper-debug "done setting zeros; now inserting mines")
  (minesweeper-insert-mines *minesweeper-mines* protect-row protect-col))

(defun minesweeper-insert-mines (count protect-row protect-col)
  "Insert COUNT mines into the minefield, and build the neighbor count.

There can't be a mine at the square (PROTECT-ROW, PROTECT-COL)"
  (minesweeper-debug "inserting " (number-to-string count) " mines")
  (let* ((square-count (1- (* *minesweeper-board-width* *minesweeper-board-height*)))
	 (mines (make-vector square-count (list 0 0)))
	 (pos 0))
    (dotimes (col *minesweeper-board-width*)
      (dotimes (row *minesweeper-board-height*)
        (unless (and (eq row protect-row)
                     (eq col protect-col))
          (minesweeper-debug "setting " (number-to-string col) "\t" (number-to-string row))
          (aset mines pos (list row col))
          (setq pos (1+ pos)))))
    (dotimes (i count)
      (let* ((rand (random (- square-count i)))
	     (ele (aref mines rand)))
	(minesweeper-debug "picked a random mine at position " (number-to-string rand) ". The mine is row:f" (number-to-string (car ele)) "\tcol: " (number-to-string (cadr ele)) ". We've picked " (number-to-string i)" mines so far.")
	(aset mines rand (aref mines (- square-count i 1)))
	(minesweeper-set-mine (car ele) (cadr ele) ?X)
	(minesweeper-inform-around (car ele) (cadr ele))))))

(defun minesweeper-position ()
    "Return the current position of point as a minesweeper position construct.

The return value is a list where the first element is the row value, the second is the col value, and the third is whether the position is in bounds."
    (let ((row (1- (line-number-at-pos)))
          (col (current-column)))
      (list row col (minesweeper-in-bounds row col))))

(defun minesweeper-view-mine (row col &optional reveal)
  "Return the visible value at position (ROW, COL).

If REVEAL is true, or if the selected mine has been revealed,
returns the actual value.  Otherwise, it returns the character *
if the square is marked, the character - if it is not."
  (minesweeper-debug "called view-mine " (number-to-string col) " " (number-to-string row) " " (if reveal "reveal!" "hide"))
  (cond ((or reveal
	     (minesweeper-is-revealed row col))
	 (gethash (list row col)
		  *minesweeper-field*))
	((minesweeper-marked row col)
	 ?*)
	('t
	 ?-)))

(defun minesweeper-is-mine (row col)
  "Return 't iff (ROW, COL) is a mine."
  (eq (minesweeper-view-mine row col 't)
      ?X))

(defun minesweeper-set-mine (row col val)
  "Set the value of the (ROW, COL) mine to VAL."
  (puthash (list row col)
	   val
	   *minesweeper-field*))

(defun minesweeper-reveal (row col)
  "Reveal (ROW, COL)."
  (puthash (list row col)
	   't
	   *minesweeper-reveals*))

(defun minesweeper-hide (row col)
  "Hide (ROW, COL)."
  (puthash (list row col)
	   nil
	   *minesweeper-reveals*))

(defun minesweeper-is-revealed (row col)
  "Return 't if (ROW, COL) is revealed, nil otherwise."
  (gethash (list row col)
	   *minesweeper-reveals*))

(defun minesweeper-mark (row col)
  "Mark the square (ROW, COL)."
  (minesweeper-debug "marking square " (number-to-string row) "\t" (number-to-string col))
  (unless (minesweeper-marked row col)
    (puthash (list row col)
	     't
	     *minesweeper-marks*)
    (setq *minesweeper-mark-count* (1+ *minesweeper-mark-count*))))

(defun minesweeper-unmark (row col)
  "Set the square (ROW, COL) as unmarked."
  (when (minesweeper-marked row col)
    (puthash (list row col)
	     nil
	     *minesweeper-marks*)
    (setq *minesweeper-mark-count* (1- *minesweeper-mark-count*))))

(defun minesweeper-invert-mark (row col)
  "If (ROW, COL) is marked, unmark it.  Otherwise, mark it."
  (when (and (minesweeper-in-bounds row col)
	     (not (minesweeper-is-revealed row col)))
    (if (minesweeper-marked row col)
	(minesweeper-unmark row col)
      (minesweeper-mark row col))))

(defun minesweeper-marked (row col)
  "Return 't if (ROW, COL) is marked, nil otherwise."
  (gethash (list row col)
	   *minesweeper-marks*))

(defun minesweeper-inform-around (row col &optional amount)
  "Increase the value of all squares around (ROW, COL) by AMOUNT."
  (mapc #'(lambda (position)
	  (minesweeper-++ (car position) (cadr position) amount))
	(minesweeper-neighbors row col)))

(defun minesweeper-++ (row col &optional amount)
  "Increment the value at square (ROW, COL) by AMOUNT, unless the square is a bomb."
  (let ((val (minesweeper-view-mine row col 't)))
    (when (and (<= ?0 val)
	       (<= val ?8))
      (minesweeper-set-mine row
			    col
			    (+ val
			       (or amount 1))))))

(defun minesweeper-neighbors (row col)
  "Return a list of the neighbors of (ROW, COL)."
  (let ((neighbors nil))
    (dolist (newcol (number-sequence (1- col)
                                     (1+ col)))
      (dolist (newrow (number-sequence (1- row)
                                       (1+ row)))
        (when (and (minesweeper-in-bounds newrow newcol)
                   (not (and (eq newcol col)
                             (eq newrow row))))
          (push (list newrow newcol)
                neighbors))))
    neighbors))

(defun minesweeper-print-field (&optional reveal)
  "Print out the minefield.

If REVEAL is true, then reveal all points, showing even squares that have not
been revealed by the user.

After printing,  put point back where it was when the function was called."
  (minesweeper-debug "Printing out the field")
  (let ((inhibit-read-only t)
        (pt (point)))
    (erase-buffer)
    (dotimes (row *minesweeper-board-height*)
      (dotimes (col *minesweeper-board-width*)
        (minesweeper-insert-value (minesweeper-view-mine row col reveal)))
      (newline))
    (unless reveal
      (insert-char ?\s *minesweeper-board-width*) ;;insert a row below the field for choosing neighbors.
      (newline)
      (insert (number-to-string *minesweeper-mark-count*)
	      " of "
	      (number-to-string *minesweeper-mines*)
	      " marked."))
    (minesweeper-debug "Field is printed out")
    (goto-char pt)))

(defun minesweeper-refresh-square (row col)
  "Refresh the printed value of (ROW, COL)."
  (minesweeper-debug "starting refresh-square. (row, col) is (" (number-to-string row) ",\t" (number-to-string col) ")")
  (when (minesweeper-in-bounds row col)
    (let ((val (minesweeper-view-mine row col)))
      (goto-char (point-min))
      (forward-line row)
      (forward-char col)
      (let ((inhibit-read-only t))
        (delete-char 1)
        (minesweeper-insert-value (minesweeper-view-mine row col)))
      (forward-char -1))))

(defun minesweeper-insert-value (val)
  "Output VAL, properly colored, at point."
  (insert-char val 1)
  (add-text-properties (point)
		       (1- (point))
		       (list 'face
			     (minesweeper-get-face val))))

(defun minesweeper-pick (row col)
  "Reveal the square at position (ROW, COL).

If the square is zero,  pick all the neighbors around (col, row)."
  (minesweeper-debug "starting pick with args:" (number-to-string row) " " (number-to-string col))
  (unless (or (not (minesweeper-in-bounds row col))
	      (minesweeper-is-revealed row col)
	      (minesweeper-marked row col))
    (minesweeper-debug "in pick, valid position chosen")
    (when *minesweeper-first-move*
      (minesweeper-debug "in pick, first-move is on. Calling view-mine.")
      (minesweeper-fill-field row col)
      (setq *minesweeper-first-move* nil))
    (minesweeper-debug "in pick, done with first-move check. Getting the value of the square.")
    (if (minesweeper-is-mine row col)
        (progn (minesweeper-lose-game row col)
               (throw 'game-end nil))
      (let ((to-reveal (list (list row col))))
        (minesweeper-debug "The user didn't pick an X")
        (while to-reveal
          (cl-multiple-value-bind (cur-row cur-col) (pop to-reveal)
            (minesweeper-debug "View-mine says " (number-to-string cur-col) ", " (number-to-string cur-row) " mine = " (make-string 1 (minesweeper-view-mine cur-row cur-col 't)))
            (unless (or (minesweeper-is-revealed cur-row cur-col)
                        (minesweeper-marked cur-row cur-col))
              (minesweeper-debug "it's not revealed, so reveal it")
              (minesweeper-reveal cur-row cur-col)
              (if (eq (setq *minesweeper-blanks-left* (1- *minesweeper-blanks-left*))
                      0)
                  (progn (minesweeper-win-game)
                         (throw 'game-end nil))
                (when (eq (minesweeper-view-mine cur-row cur-col 't)
                          ?0)
                  (minesweeper-debug "pushing neighbors onto the stack")
                  (mapc #'(lambda (position)
                           (push position
                                 to-reveal))
                        (minesweeper-neighbors cur-row cur-col)))))))))))


(defun minesweeper-toggle-mark ()
  "Set the marked status of the current square to the opposite of what it currently is."
  (interactive)
  (unless *minesweeper-game-over*
    (cl-multiple-value-bind (row col in-bounds) (minesweeper-position)
      (when in-bounds
        (minesweeper-invert-mark row col)
        (minesweeper-print-field)))))

(defun minesweeper-toggle-mark-mouse (click)
  "Invert the marked status of the clicked-on square.

CLICK is the input event corresponding to the mouse click."
  (interactive "e")
  (unless *minesweeper-game-over*
    (let* ((window (elt (cadr click) 0))
	   (pos (elt (cadr click) 6))
	   (col (car pos))
	   (row (cdr pos)))
      (when (minesweeper-in-bounds row col)
        (minesweeper-invert-mark row col)
        (select-window window)
        (minesweeper-print-field))
      (when (minesweeper-neighbors-bounds row col)
        (goto-char 0)
        (forward-line row)
        (forward-char col)))))


(defun minesweeper-choose ()
  "This is the function called when the user picks a mine."
  (interactive)
  (minesweeper-debug "starting choose")
  (unless *minesweeper-game-epoch*
    (setq *minesweeper-game-epoch* (current-time)))
  (unless *minesweeper-game-over*
    (cl-multiple-value-bind (row col in-bounds) (minesweeper-position)
      (when in-bounds
        (catch 'game-end (minesweeper-pick row col)
               (if (eq (minesweeper-view-mine row col) ?0)
                   (minesweeper-print-field)
                 (minesweeper-refresh-square row col))))
      (minesweeper-debug "finishing choose"))))

(defun minesweeper-choose-around ()
  "Choose all non-marked cells around point.

It does not include the cell at point."
  (interactive)
  (minesweeper-debug "starting choose-around")
  (unless *minesweeper-game-over*
    (cl-multiple-value-bind (row col) (minesweeper-position)
      (when (minesweeper-neighbors-bounds row col)
        (catch 'game-end (minesweeper-pick-around row col)
               (minesweeper-print-field)))
      (minesweeper-debug "finishing choose-round"))))

(defun minesweeper-choose-around-mouse (click)
  "Choose all the non-marked cells around the one clicked on.

CLICK is the input event corresponding to the mouse click."
  (interactive "e")
  (minesweeper-debug "beginning choose-around-mouse")
  (unless *minesweeper-game-over*
    (let* ((window (elt (cadr click) 0))
           (pos (elt (cadr click) 6))
           (row (cdr pos))
           (col (car pos)))
      (select-window window)
      (when (minesweeper-neighbors-bounds row col)
        (goto-char 0)
        (forward-line row)
        (forward-char col))
      (catch 'game-end (minesweeper-pick-around row col)
	     (minesweeper-print-field))))
  (minesweeper-debug "ending choose-around-mouse"))

(defun minesweeper-pick-around (row col)
  "Pick all the squares around but not including (ROW, COL)."
  (minesweeper-debug "called pick-around " (number-to-string row) " " (number-to-string col))
  (when (minesweeper-neighbors-bounds row col)
    (mapc #'(lambda (position)
	     (minesweeper-debug "called pick-around-helper " (number-to-string col) " " (number-to-string row))
	     (minesweeper-pick (car position) (cadr position)))
	  (minesweeper-neighbors row col))))

(defun minesweeper-lose-game (row col)
  "Print the lose-game message and prompt for a new one.

\(ROW, COL) is the square the user clicked on that contained a mine"
  (setq *minesweeper-losses* (1+ *minesweeper-losses*))
  (minesweeper-end-game nil))

(defun minesweeper-win-game ()
  "Print the win-game message and prompt for a new one."
  (setq *minesweeper-wins* (1+ *minesweeper-wins*))
  (minesweeper-end-game 't))

(defun minesweeper-end-game (won)
  "End the game.

More specifically: print the revealed minefield and prompt for a new game.

This should be called immediately after selecting the winning or losing square,
so point is still on that square.  WON should be whether the user has won the game."
  (setq *minesweeper-game-over* 't)
  (minesweeper-print-field 't)
  (cl-multiple-value-bind (row col) (minesweeper-position)
      (unless won
        (let ((point (+ (* row
                           (1+ *minesweeper-board-width*)) ;;the new line at the end of the board counts as a character
                        col
                        1)));; (point) is 1-based
          (move-overlay *minesweeper-explode-overlay*
                        point
                        (1+ point)
                        (get-buffer "minesweeper")))
        (dotimes (newrow *minesweeper-board-height*)
          (dotimes (newcol *minesweeper-board-width*)
            (when (and (minesweeper-marked newrow newcol)
                       (not (minesweeper-is-mine newrow newcol)))
              (let ((pt (+ (* newrow
                              (1+ *minesweeper-board-height*))
                           newcol
                           1)))
                (minesweeper-debug "(" (number-to-string newrow) ", " (number-to-string newcol) ") is mismarked.")
                (move-overlay (copy-overlay *minesweeper-mismarked-overlay*)
                              pt
                              (1+ pt)
                              (get-buffer "minesweeper"))))))))
  (when (y-or-n-p (if won
                      (concat "Congrats! You've won in "
                              (minesweeper-game-duration-message)
                              ". "
                              (minesweeper-record-message)
                              "Another game? ")
                    (concat "Sorry, you lost. You chose a bomb. This game took "
                            (minesweeper-game-duration-message)
                            ". "
                            (minesweeper-record-message)
                            "Another game? ")))
    (minesweeper-begin-game *minesweeper-board-width* *minesweeper-board-height* *minesweeper-mines*)))


(defun minesweeper-game-duration-message ()
  "Return the duration the current game has taken as a human-readable string."
  (let ((game-duration (time-subtract (current-time) *minesweeper-game-epoch*)))
    (format-seconds "%H, %M, %z%S" (+ (* (car game-duration)
					 (expt 2 16))
				      (cadr game-duration)))))

(defun minesweeper-record-message ()
  "Return the number of wins and losses formatted as a human-readable string."
  (concat "You've won "
	  (number-to-string *minesweeper-wins*)
	  " game"
          (unless (= *minesweeper-wins*
                     1)
            "s")
          " and lost "
	  (number-to-string *minesweeper-losses*)
	  ". "))

(defun minesweeper-get-integer (&optional message default)
  "Read one nonzero integer from the minibuffer.

Use MESSAGE as the prompt message.
Default the input to DEFAULT"
  (setq default (cond ((not default)
		       "0")
		      ((integerp default)
		       (number-to-string default))
		      ((stringp default)
		       default)
		      (t "0")))
  (let ((val (string-to-number (read-string (concat (or message "Input an integer")
						    " (default "
						    default
						    "):")
					    nil nil default))))
    (while (eq val 0)
      (setq val (string-to-number (read-string (concat (or message "Input an integer")
						       ". Please, a nonzero integer. Try again. (default "
						       default
						       "):")
					       nil nil default))))
    val))

(defun minesweeper-show-neighbors ()
  "If point is within the minefield, highlight as many of the eight squares around point that are in the minefield."
  (minesweeper-reset-neighbor-overlays)
  (when (equal "minesweeper"
	       (buffer-name (current-buffer)))
    (cl-multiple-value-bind (row col) (minesweeper-position)
      (let ((point (point)))
        (when (minesweeper-neighbors-bounds row col)
          (when (> row 0) ;; "top" overlay
            (let ((center (- point *minesweeper-board-width* 1)))
              (move-overlay *minesweeper-top-overlay*
                            (- center (min col 1))
                            (+ center (cond ((< col (1- *minesweeper-board-width*)) 2)
                                            ((= col (1- *minesweeper-board-width*)) 1)
                                            ((> col (1- *minesweeper-board-width*)) 0)))
                            (get-buffer "minesweeper"))))
          (when (> col 0) ;; "left" overlay
            (move-overlay *minesweeper-left-overlay* (1- point) point (get-buffer "minesweeper")))
          (when (< col (1- *minesweeper-board-width*)) ;; "right" overlay
            (move-overlay *minesweeper-right-overlay* (1+ point) (+ point 2) (get-buffer "minesweeper")))
          (when (< row (1- *minesweeper-board-height*)) ;; "bottom" overlay
            (let ((center (+ point *minesweeper-board-width* 1)))
              (move-overlay *minesweeper-bottom-overlay*
                            (- center (if (eq col 0) 0 1))
                            (+ center (cond ((< col (1- *minesweeper-board-width*)) 2)
                                            ((= col (1- *minesweeper-board-width*)) 1)
                                            ((> col (1- *minesweeper-board-width*)) 0)))
                            (get-buffer "minesweeper")))))))))

(defun minesweeper-get-face (val)
  "Get the face for the character value of VAL.

Proper inputs are ?0 through ?8, ?- and ?*"
  (gethash val *minesweeper-faces*))

(defun minesweeper-toggle-show-neighbors ()
  "Toggle whether neighbors are shown."
  (interactive)
  (if *minesweeper-idle-timer*
      (progn (cancel-timer *minesweeper-idle-timer*)
	     (minesweeper-reset-neighbor-overlays)
	     (setq *minesweeper-idle-timer* nil))
    (setq *minesweeper-idle-timer* (run-with-idle-timer *minesweeper-idle-delay*
							t
							'minesweeper-show-neighbors))))

(defun minesweeper-reset-neighbor-overlays ()
  "Move all the neighbor overlays to the beginning of the buffer.

Moving them there ensures they won't be seen."
  (move-overlay *minesweeper-top-overlay* 0 0 (get-buffer "minesweeper"))
  (move-overlay *minesweeper-left-overlay* 0 0 (get-buffer "minesweeper"))
  (move-overlay *minesweeper-right-overlay* 0 0 (get-buffer "minesweeper"))
  (move-overlay *minesweeper-bottom-overlay* 0 0 (get-buffer "minesweeper")))

(defun minesweeper-in-bounds (row col)
  "Return 't iff (ROW, COL) is inside the bounds of the minefield."
  (minesweeper-debug "Called in-bounds with arguments " (number-to-string col) "\t" (number-to-string row) "\treturning " (if (and (< -1 col)
       (< col *minesweeper-board-width*)
       (< -1 row)
       (< row *minesweeper-board-height*)) "t" "nil"))
  (and (< -1 col)
       (< col *minesweeper-board-width*)
       (< -1 row)
       (< row *minesweeper-board-height*)))

(defun minesweeper-neighbors-bounds (row col)
  "Return 't iff (ROW, COL) has at least one neighbor in the minefield.

I.e., (row, col) is in the minefield, or it neighbors the minefield."
    (and (<= -1 col) ;;Right now, you can't get negative rows or columns. Maybe in the future?
       (<= col *minesweeper-board-width*)
       (<= -1 row)
       (<= row *minesweeper-board-height*)))

(provide 'minesweeper)
;;; minesweeper.el ends here
