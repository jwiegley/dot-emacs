;;; gnugo-imgen.el --- image generation         -*- lexical-binding: t -*-

;; Copyright (C) 2014  Free Software Foundation, Inc.

;; Author: Thien-Thi Nguyen <ttn@gnu.org>
;; Maintainer: Thien-Thi Nguyen <ttn@gnu.org>

;; This program is free software; you can redistribute it and/or modify
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

;; This file provides func `gnugo-imgen-create-xpms', suitable as
;; value for `gnugo-xpms', and several variables to configure it:
;;
;;  `gnugo-imgen-styles'
;;  `gnugo-imgen-style'
;;  `gnugo-imgen-sizing-function'
;;
;; There is also one command: `gnugo-imgen-clear-cache'.

;;; Code:

(require 'xpm)
(require 'xpm-m2z)
(require 'cl-lib)

(defvar gnugo-imgen-styles
  '((d-bump                             ; thanks
     :background "#FFFFC7C75252"
     :grid-lines "#000000000000"
     :circ-edges "#C6C6C3C3C6C6"
     :white-fill "#FFFFFFFFFFFF"
     :black-fill "#000000000000")
    (ttn                                ; this guy must live in a cave
     :background "#000000000000"
     :grid-lines "#AAAA88885555"
     :circ-edges "#888888888888"
     :white-fill "#CCCCCCCCCCCC"
     :black-fill "#444444444444"))
  "Alist of styles suitable for `gnugo-imgen-create-xpms'.
The key is a symbol naming the style.  The value is a plist.
Here is a list of recognized keywords and their meanings:

 :background -- string that names a color in XPM format, such as
 :grid-lines    \"#000000000000\" or \"black\"; the special string
 :circ-edges    \"None\" makes that component transparent
 :white-fill
 :black-fill

All keywords are required and color values cannot be nil.
This restriction may be lifted in the future.")

(defvar gnugo-imgen-style nil
  "Which style in `gnugo-imgen-styles' to use.
If nil, `gnugo-imgen-create-xpms' defaults to the first one.")

(defvar gnugo-imgen-sizing-function 'gnugo-imgen-fit-window-height
  "Function to compute XPM image size from board size.
This is called with one arg, integer BOARD-SIZE, and should return
a number (float or integer), the number of pixels for the side of
a square position on the board.  A value less than 8 is taken as 8.")

(defvar gnugo-imgen-cache (make-hash-table :test 'equal))

(defun gnugo-imgen-clear-cache ()
  "Clear the cache."
  (interactive)
  (clrhash gnugo-imgen-cache))

(defun gnugo-imgen-fit-window-height (board-size)
  "Return the dimension (in pixels) of a square for BOARD-SIZE.
This uses the TOP and BOTTOM components as returned by
`window-inside-absolute-pixel-edges' and subtracts twice
the `frame-char-height' (to leave space for the grid)."
  (cl-destructuring-bind (L top R bot)
      (window-inside-absolute-pixel-edges)
    (ignore L R)
    (/ (float (- bot top (* 2 (frame-char-height))))
       board-size)))

(defconst gnugo-imgen-palette '((32 . :background)
                                (?. . :grid-lines)
                                (?X . :circ-edges)
                                (?- . :black-fill)
                                (?+ . :white-fill)))

(defun gnugo-imgen-create-xpms-1 (square style)
  (let* ((kws (mapcar 'cdr gnugo-imgen-palette))
         (roles (mapcar 'symbol-name kws))
         (palette (cl-loop
                   for px in (mapcar 'car gnugo-imgen-palette)
                   for role in roles
                   collect (cons px (format "s %s" role))))
         (resolved (cl-loop
                    with parms = (copy-sequence style)
                    for role in roles
                    for kw in kws
                    collect (cons role (plist-get parms kw))))
         (sq-m1 (1- square))
         (half (/ sq-m1 2.0))
         (half-m1 (truncate (- half 0.5)))
         (half-p1 (truncate (+ half 0.5)))
         (background (make-vector 10 nil))
         (foreground (make-vector 4 nil))
         rv)
    (cl-flet
        ((workbuf (n)
                  (xpm-generate-buffer (format "%d_%d" n square)
                                       square square 1 palette))
         (replace-from (buffer)
                       (erase-buffer)
                       (insert-buffer-substring buffer)
                       (xpm-grok t))
         (nine-from-four (N E W S)
                         (list (list   E   S)
                               (list   E W S)
                               (list     W S)
                               (list N E   S)
                               (list N E W S)
                               (list N   W S)
                               (list N E    )
                               (list N E W  )
                               (list N   W  )))
         (mput-points (px ls)
                      (dolist (coord ls)
                        (apply 'xpm-put-points px coord))))
      ;; background
      (cl-loop
       for place from 1 to 9
       for parts
       in (cl-flet*
              ((vline (x y1 y2)  (list (list x (cons y1 y2))))
               (v-expand (y1 y2) (append (vline half-m1 y1 y2)
                                         (vline half-p1 y1 y2)))
               (hline (y x1 x2)  (list (list (cons x1 x2) y)))
               (h-expand (x1 x2) (append (hline half-m1 x1 x2)
                                         (hline half-p1 x1 x2))))
            (nine-from-four (v-expand 0       half-p1)
                            (h-expand half-m1   sq-m1)
                            (h-expand 0       half-p1)
                            (v-expand half-m1   sq-m1)))
       do (aset background place
                (with-current-buffer (workbuf place)
                  (dolist (part parts)
                    (mput-points ?. part))
                  (current-buffer))))
      ;; foreground
      (cl-flet
          ((circ (radius)
                 (xpm-m2z-circle half half radius)))
        (cl-loop
         with stone = (circ (truncate half))
         with minim = (circ (/ square 9))
         for n below 4
         do (aset foreground n
                  (with-current-buffer (workbuf n)
                    (cl-flet
                        ((rast (form b w)
                               (xpm-raster form ?X
                                           (if (> 2 n)
                                               b
                                             w))))
                      (if (cl-evenp n)
                          (rast stone ?- ?+)
                        (replace-from (aref foreground (1- n)))
                        (rast minim ?+ ?-))
                      (current-buffer))))))
      ;; do it
      (cl-flet
          ((ok (place type finish)
               (goto-char 25)
               (delete-char (- (skip-chars-forward "^1-9")))
               (delete-char 1)
               (insert (format "%s%d" type place))
               (push (cons (cons type place)
                           (funcall finish
                                    :ascent 'center
                                    :color-symbols resolved))
                     rv)))
        (with-current-buffer (workbuf 5)
          (replace-from (aref background 5))
          (xpm-raster
           ;; yes, using an ellipse is bizarre; no, we don't mind;
           ;; maybe, ‘artist-ellipse-generate-quadrant’ is stable.
           (xpm-m2z-ellipse half half 4 4.5)
           ?. t)
          (ok 5 'hoshi 'xpm-finish))
        (cl-loop
         for place from 1 to 9
         for decor in (let ((friends (cons half-m1 half-p1)))
                        (nine-from-four (list friends       0)
                                        (list sq-m1   friends)
                                        (list 0       friends)
                                        (list friends   sq-m1)))
         do (with-current-buffer (aref background place)
              (ok place 'empty 'xpm-finish))
         do (cl-flet
                ((decorate (px)
                           (mput-points px decor)))
              (cl-loop
               for n below 4
               for type in '(bmoku bpmoku wmoku wpmoku)
               do (with-current-buffer (aref foreground n)
                    (decorate ?.)
                    (ok place type 'xpm-as-xpm)
                    (decorate 32)))))
        (mapc 'kill-buffer foreground)
        (nreverse rv)))))

;;;###autoload
(defun gnugo-imgen-create-xpms (board-size)
  "Return a list of XPM images suitable for BOARD-SIZE.
The size and style of the images are determined by
`gnugo-imgen-sizing-function' (rounded down to an even number)
and `gnugo-imgen-style', respectively.  See `gnugo-xpms'.

The returned list is cached; see also `gnugo-imgen-clear-cache'."
  (let* ((square (let ((n (funcall gnugo-imgen-sizing-function
                                   board-size)))
                   (unless (numberp n)
                     (error "Invalid BOARD-SIZE: %s" board-size))
                   (max 8 (logand (lognot 1) (truncate n)))))
         (style (or (unless gnugo-imgen-style (cdar gnugo-imgen-styles))
                    (cdr (assq gnugo-imgen-style gnugo-imgen-styles))
                    (error "No style selected")))
         (key (cons square style)))
    (or (gethash key gnugo-imgen-cache)
        (puthash key (gnugo-imgen-create-xpms-1 square style)
                 gnugo-imgen-cache))))

;;;---------------------------------------------------------------------------
;;; that's it

(provide 'gnugo-imgen)

;;; gnugo-imgen.el ends here
